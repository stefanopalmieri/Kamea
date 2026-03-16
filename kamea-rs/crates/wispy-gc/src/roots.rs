//! Shadow stack for root scanning.
//!
//! The shadow stack holds WispyVal entries that may contain heap pointers.
//! Before any allocation that might trigger GC, the transpiler emits
//! shadow_push() for live heap values. After the allocation, shadow_pop().
//!
//! During GC, scan_roots_in_mutator_thread walks the shadow stack and
//! reports each entry as a WispySlot. If MMTk copies the referenced object,
//! it updates the entry in-place via WispySlot::store().

use mmtk::util::Address;
use std::sync::Mutex;

use crate::WispyVal;

/// The shadow stack is a vector of WispyVal stored at known addresses
/// so the GC can update them in-place.
pub struct ShadowStack {
    /// Each entry is a boxed WispyVal so its address is stable.
    entries: Vec<Box<WispyVal>>,
}

impl ShadowStack {
    pub fn new() -> Self {
        ShadowStack {
            entries: Vec::with_capacity(256),
        }
    }

    /// Push a value onto the shadow stack. Returns the index for pop.
    pub fn push(&mut self, val: WispyVal) -> usize {
        let idx = self.entries.len();
        self.entries.push(Box::new(val));
        idx
    }

    /// Pop n entries from the shadow stack.
    pub fn pop(&mut self, n: usize) {
        let new_len = self.entries.len().saturating_sub(n);
        self.entries.truncate(new_len);
    }

    /// Read back a value (may have been updated by GC).
    pub fn get(&self, idx: usize) -> WispyVal {
        *self.entries[idx]
    }

    /// Get the addresses of all entries for root scanning.
    pub fn slots(&self) -> Vec<Address> {
        self.entries
            .iter()
            .map(|entry| {
                let ptr: *const WispyVal = &**entry;
                unsafe { Address::from_usize(ptr as usize) }
            })
            .collect()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

lazy_static::lazy_static! {
    pub static ref SHADOW_STACK: Mutex<ShadowStack> = Mutex::new(ShadowStack::new());
}

/// Push a value onto the shadow stack (called by generated code).
pub fn shadow_push(val: WispyVal) -> usize {
    SHADOW_STACK.lock().unwrap().push(val)
}

/// Pop n values from the shadow stack (called by generated code).
pub fn shadow_pop(n: usize) {
    SHADOW_STACK.lock().unwrap().pop(n);
}

/// Read a value from the shadow stack (may have been updated by GC).
pub fn shadow_get(idx: usize) -> WispyVal {
    SHADOW_STACK.lock().unwrap().get(idx)
}
