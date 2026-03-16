//! wispy-gc: MMTk garbage collector integration for compiled Ψ∗ programs.
//!
//! WispY has exactly one heap-allocated type: cons cells (car: i64, cdr: i64).
//! This is the simplest possible object model for a GC.
//!
//! Phase 2 will replace the bump allocator in psi_runtime.rs with MMTk-managed
//! allocation so that compiled programs can run indefinitely without OOM.

pub mod vm;
pub mod object;
pub mod roots;
pub mod alloc;

pub use alloc::{wispy_cons, wispy_car, wispy_cdr, wispy_init, wispy_init_with_heap, wispy_shutdown};
pub use roots::{shadow_push, shadow_pop, shadow_get};

/// Value representation — same as psi_runtime.rs.
/// All values are i64. Numbers are plain integers.
/// NIL is a special sentinel. Cons cells use a tag bit.
pub type WispyVal = i64;

pub const WISPY_NIL: WispyVal = i64::MIN;
pub const WISPY_CONS_TAG: WispyVal = 1_i64 << 62;

#[inline(always)]
pub fn is_nil(v: WispyVal) -> bool {
    v == WISPY_NIL
}

#[inline(always)]
pub fn is_cons(v: WispyVal) -> bool {
    (v & WISPY_CONS_TAG) != 0 && v != WISPY_NIL
}

#[inline(always)]
pub fn is_true(v: WispyVal) -> bool {
    v != WISPY_NIL
}

/// Convert a tagged WispyVal to a raw heap address (strips tag).
#[inline(always)]
pub fn val_to_addr(v: WispyVal) -> usize {
    (v & !WISPY_CONS_TAG) as usize
}

/// Convert a raw heap address to a tagged WispyVal (adds tag).
#[inline(always)]
pub fn addr_to_val(addr: usize) -> WispyVal {
    WISPY_CONS_TAG | (addr as WispyVal)
}
