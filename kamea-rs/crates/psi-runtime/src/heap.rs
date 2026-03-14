use psi_core::term::Arena;

/// Wraps Arena with growth policy.
pub struct Heap {
    pub arena: Arena,
}

impl Heap {
    pub fn new(capacity: usize) -> Self {
        Heap {
            arena: Arena::new(capacity),
        }
    }
}
