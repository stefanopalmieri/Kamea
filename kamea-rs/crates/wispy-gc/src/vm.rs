//! WispyVM: the VMBinding implementation for MMTk.
//!
//! Single-threaded runtime with one object type (cons cells).

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

// ── WispySlot: tagged pointer slot ──────────────────────────────────

use mmtk::util::{Address, ObjectReference};
use std::fmt;

/// A slot that holds a tagged WispyVal (i64).
/// Cons cell pointers have PSI_CONS_TAG (bit 62) set.
/// Integers and NIL are not heap references.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct WispySlot {
    /// Address of the i64 field in memory (car or cdr of a cons cell, or shadow stack entry).
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
            None // integer or NIL — not a heap reference
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
        // A cons cell has two fields: car at +0, cdr at +8 from ObjectReference
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
        // Scan the shadow stack for roots.
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
        // No VM-specific roots beyond the shadow stack (handled in mutator scan).
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {
        // Nothing to do for single-threaded.
    }

    fn supports_return_barrier() -> bool {
        false
    }

    fn prepare_for_roots_re_scanning() {
        // Nothing to do.
    }
}

// ── Collection ──────────────────────────────────────────────────────

impl Collection<WispyVM> for WispyVM {
    fn stop_all_mutators<F>(_tls: VMWorkerThread, mut mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<WispyVM>),
    {
        // Single-threaded: the one mutator is already stopped (we're in GC).
        // Visit it so MMTk can scan its allocator state.
        unsafe {
            if let Some(m) = crate::alloc::MUTATOR.as_mut() {
                mutator_visitor(&mut **m);
            }
        }
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        // Single-threaded: nothing to resume.
    }

    fn block_for_gc(_tls: VMMutatorThread) {
        // Single-threaded: GC runs synchronously, so this is a no-op.
        // The mutator IS the GC thread.
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<WispyVM>) {
        match ctx {
            GCThreadContext::Worker(worker) => {
                std::thread::spawn(move || {
                    let tls = VMWorkerThread(VMThread::UNINITIALIZED);
                    mmtk::memory_manager::start_worker(
                        crate::alloc::mmtk_ref(),
                        tls,
                        worker,
                    );
                });
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
        true // single-threaded: everything is the mutator
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

// ── ReferenceGlue (stub — no weak refs) ─────────────────────────────

impl ReferenceGlue<WispyVM> for WispyVM {
    type FinalizableType = ObjectReference;

    fn clear_referent(_new_reference: ObjectReference) {
        // No weak references in WispY.
    }

    fn get_referent(_object: ObjectReference) -> Option<ObjectReference> {
        None
    }

    fn set_referent(_reff: ObjectReference, _referent: ObjectReference) {
        // No weak references.
    }

    fn enqueue_references(_references: &[ObjectReference], _tls: VMWorkerThread) {
        // No weak references.
    }
}
