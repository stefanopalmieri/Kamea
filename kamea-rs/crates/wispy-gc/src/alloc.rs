//! Allocation API: wispy_cons, wispy_car, wispy_cdr.
//!
//! These have the same semantics as Arena::cons/car/cdr but allocate
//! through MMTk instead of a bump allocator.

use mmtk::memory_manager;
use mmtk::AllocationSemantics;
use mmtk::util::{Address, ObjectReference};
use mmtk::Mutator;
use mmtk::MMTK;

use crate::object::{CDR_OFFSET, CONS_CELL_SIZE, HEADER_SIZE};
use crate::vm::WispyVM;
use crate::{WispyVal, WISPY_NIL};

/// Global MMTk instance (leaked Box for 'static lifetime).
static mut MMTK_INSTANCE: Option<&'static MMTK<WispyVM>> = None;

/// Global mutator (single-threaded).
pub static mut MUTATOR: Option<Box<Mutator<WispyVM>>> = None;

/// Get a reference to the global MMTK instance.
pub fn mmtk_ref() -> &'static MMTK<WispyVM> {
    unsafe { MMTK_INSTANCE.expect("MMTk not initialized") }
}

/// Initialize the MMTk GC. Call once at program start.
pub fn wispy_init() {
    let builder = mmtk::MMTKBuilder::new();
    // Use NoGC for initial bring-up; switch to MarkSweep/SemiSpace later
    // builder.options.plan.set(mmtk::util::options::PlanSelector::NoGC);

    let mmtk: Box<MMTK<WispyVM>> = memory_manager::mmtk_init(&builder);
    let mmtk_static: &'static MMTK<WispyVM> = Box::leak(mmtk);

    unsafe {
        MMTK_INSTANCE = Some(mmtk_static);
    }

    // Create the single mutator
    let tls = mmtk::util::opaque_pointer::VMMutatorThread(
        mmtk::util::opaque_pointer::VMThread::UNINITIALIZED,
    );
    let mutator = memory_manager::bind_mutator(mmtk_static, tls);

    unsafe {
        MUTATOR = Some(mutator);
    }
}

/// Shut down the MMTk GC. Call at program end.
pub fn wispy_shutdown() {
    unsafe {
        MUTATOR = None;
        MMTK_INSTANCE = None;
    }
}

/// Allocate a new cons cell via MMTk.
///
/// Returns a tagged WispyVal with WISPY_CONS_TAG set.
pub fn wispy_cons(car: WispyVal, cdr: WispyVal) -> WispyVal {
    let mutator = unsafe {
        MUTATOR
            .as_mut()
            .expect("mutator not initialized — call wispy_init() first")
    };

    // Allocate 24 bytes (header + car + cdr)
    let addr = memory_manager::alloc(
        mutator,
        CONS_CELL_SIZE,
        8, // alignment
        0, // offset
        AllocationSemantics::Default,
    );

    if addr.is_zero() {
        eprintln!("wispy-gc: allocation failed");
        std::process::exit(1);
    }

    // Initialize: zero the header, write car and cdr
    unsafe {
        addr.store::<u64>(0); // header = 0
        (addr + HEADER_SIZE).store::<i64>(car); // car
        (addr + HEADER_SIZE + 8usize).store::<i64>(cdr); // cdr
    }

    // ObjectReference points past the header
    let obj_ref = ObjectReference::from_raw_address(addr + HEADER_SIZE).unwrap();

    // Post-alloc: initialize MMTk metadata
    memory_manager::post_alloc(mutator, obj_ref, CONS_CELL_SIZE, AllocationSemantics::Default);

    // Return tagged value
    crate::addr_to_val(obj_ref.to_raw_address().as_usize())
}

/// Read the car field of a cons cell.
pub fn wispy_car(cell: WispyVal) -> WispyVal {
    if !crate::is_cons(cell) {
        return WISPY_NIL;
    }
    let addr = unsafe { Address::from_usize(crate::val_to_addr(cell)) };
    unsafe { addr.load() }
}

/// Read the cdr field of a cons cell.
pub fn wispy_cdr(cell: WispyVal) -> WispyVal {
    if !crate::is_cons(cell) {
        return WISPY_NIL;
    }
    let addr = unsafe { Address::from_usize(crate::val_to_addr(cell)) };
    unsafe { (addr + CDR_OFFSET).load() }
}
