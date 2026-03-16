//! WispyVM: the VMBinding implementation for MMTk.
//!
//! Single-threaded runtime with one object type (cons cells).

use std::sync::{Condvar, Mutex};

use mmtk::util::alloc::AllocationError;
use mmtk::util::opaque_pointer::*;
use mmtk::vm::*;
use mmtk::vm::slot::{Slot, UnimplementedMemorySlice};
use mmtk::Mutator;

use crate::roots::SHADOW_STACK;

/// The WispY VM binding type.
#[derive(Default)]
pub struct WispyVM;

impl VMBinding for WispyVM {
    type VMObjectModel = WispyVM;
    type VMScanning = WispyVM;
    type VMCollection = WispyVM;
    type VMActivePlan = WispyVM;
    type VMReferenceGlue = WispyVM;
    type VMSlot = WispySlot;
    type VMMemorySlice = UnimplementedMemorySlice<WispySlot>;

    const MIN_ALIGNMENT: usize = 8;
    const MAX_ALIGNMENT: usize = 8;
}

// ── GC synchronization for single-threaded stop-the-world ──────────

lazy_static::lazy_static! {
    /// Condvar for blocking the mutator during GC.
    static ref GC_LOCK: Mutex<bool> = Mutex::new(false);
    static ref GC_CONDVAR: Condvar = Condvar::new();
}

// ── WispySlot: tagged pointer slot ──────────────────────────────────

use mmtk::util::{Address, ObjectReference};
use std::fmt;

/// A slot that holds a tagged WispyVal (i64).
/// Cons cell pointers have WISPY_CONS_TAG (bit 62) set.
/// Integers and NIL are not heap references.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct WispySlot {
    pub addr: Address,
}

impl fmt::Debug for WispySlot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "WispySlot({:?})", self.addr)
    }
}

unsafe impl Send for WispySlot {}

impl Slot for WispySlot {
    fn load(&self) -> Option<ObjectReference> {
        let val: i64 = unsafe { self.addr.load() };
        if crate::is_cons(val) {
            let raw_addr = crate::val_to_addr(val);
            ObjectReference::from_raw_address(unsafe { Address::from_usize(raw_addr) })
        } else {
            None
        }
    }

    fn store(&self, object: ObjectReference) {
        let tagged = crate::addr_to_val(object.to_raw_address().as_usize());
        unsafe { self.addr.store(tagged) }
    }
}

// ── Scanning ────────────────────────────────────────────────────────

impl Scanning<WispyVM> for WispyVM {
    fn scan_object<SV: SlotVisitor<WispySlot>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        let obj_addr = object.to_raw_address();
        slot_visitor.visit_slot(WispySlot { addr: obj_addr });
        slot_visitor.visit_slot(WispySlot {
            addr: obj_addr + crate::object::CDR_OFFSET,
        });
    }

    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut Mutator<WispyVM>,
        mut factory: impl RootsWorkFactory<WispySlot>,
    ) {
        let shadow = SHADOW_STACK.lock().unwrap();
        let mut slots = Vec::new();
        for entry_ptr in shadow.slots() {
            slots.push(WispySlot { addr: entry_ptr });
        }
        if !slots.is_empty() {
            factory.create_process_roots_work(slots);
        }
    }

    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        _factory: impl RootsWorkFactory<WispySlot>,
    ) {
        // No VM-specific roots beyond the shadow stack.
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {}

    fn supports_return_barrier() -> bool {
        false
    }

    fn prepare_for_roots_re_scanning() {}
}

// ── Collection ──────────────────────────────────────────────────────

impl Collection<WispyVM> for WispyVM {
    fn stop_all_mutators<F>(_tls: VMWorkerThread, mut mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<WispyVM>),
    {
        // Wait for the mutator to signal it's blocked.
        loop {
            let locked = GC_LOCK.lock().unwrap();
            if *locked {
                break;
            }
            drop(locked);
            std::thread::yield_now();
        }
        // Visit the single mutator so MMTk scans its allocator state.
        unsafe {
            if let Some(m) = crate::alloc::MUTATOR.as_mut() {
                mutator_visitor(&mut **m);
            }
        }
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        let mut locked = GC_LOCK.lock().unwrap();
        *locked = false;
        GC_CONDVAR.notify_all();
    }

    fn block_for_gc(_tls: VMMutatorThread) {
        // Called on the mutator thread when allocation triggers GC.
        let mut locked = GC_LOCK.lock().unwrap();
        *locked = true;
        while *locked {
            locked = GC_CONDVAR.wait(locked).unwrap();
        }
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<WispyVM>) {
        match ctx {
            GCThreadContext::Worker(worker) => {
                std::thread::Builder::new()
                    .name("wispy-gc-worker".to_string())
                    .spawn(move || {
                        let tls = VMWorkerThread(VMThread::UNINITIALIZED);
                        mmtk::memory_manager::start_worker(
                            crate::alloc::mmtk_ref(),
                            tls,
                            worker,
                        );
                    })
                    .expect("failed to spawn GC worker thread");
            }
        }
    }

    fn out_of_memory(_tls: VMThread, _err_kind: AllocationError) {
        eprintln!("wispy-gc: out of memory");
        std::process::exit(1);
    }
}

// ── ActivePlan ──────────────────────────────────────────────────────

impl ActivePlan<WispyVM> for WispyVM {
    fn is_mutator(_tls: VMThread) -> bool {
        true
    }

    fn mutator(_tls: VMMutatorThread) -> &'static mut Mutator<WispyVM> {
        unsafe {
            crate::alloc::MUTATOR
                .as_mut()
                .expect("mutator not initialized")
        }
    }

    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<WispyVM>> + 'a> {
        unsafe {
            if let Some(m) = crate::alloc::MUTATOR.as_mut() {
                Box::new(std::iter::once(&mut **m))
            } else {
                Box::new(std::iter::empty())
            }
        }
    }

    fn number_of_mutators() -> usize {
        1
    }
}

// ── ReferenceGlue (stub) ────────────────────────────────────────────

impl ReferenceGlue<WispyVM> for WispyVM {
    type FinalizableType = ObjectReference;

    fn clear_referent(_new_reference: ObjectReference) {}
    fn get_referent(_object: ObjectReference) -> Option<ObjectReference> { None }
    fn set_referent(_reff: ObjectReference, _referent: ObjectReference) {}
    fn enqueue_references(_references: &[ObjectReference], _tls: VMWorkerThread) {}
}
