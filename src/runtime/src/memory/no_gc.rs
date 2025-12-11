use std::sync::{Arc, Mutex};

use simple_common::gc::GcAllocator;

/// Minimal allocator that satisfies the `GcAllocator` contract without tracing.
///
/// This is the "GC-off" profile: allocations are backed by boxed buffers that live
/// for the lifetime of the allocator. `collect` is a no-op.
#[derive(Clone, Default)]
pub struct NoGcAllocator {
    allocations: Arc<Mutex<Vec<Box<[u8]>>>>,
}

impl NoGcAllocator {
    pub fn new() -> Self {
        Self::default()
    }
}

impl GcAllocator for NoGcAllocator {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize {
        super::alloc_bytes_tracked(bytes, &self.allocations)
    }

    fn collect(&self) {
        // No GC in this profile.
    }
}
