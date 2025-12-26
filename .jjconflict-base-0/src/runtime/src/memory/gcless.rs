use std::sync::{Arc, Mutex};

use simple_common::gc::GcAllocator;

/// Minimal allocator that satisfies the `GcAllocator` contract without tracing.
///
/// This is the "gcless" profile: allocations are backed by boxed buffers that live
/// for the lifetime of the allocator. `collect` is a no-op.
#[derive(Clone, Default)]
pub struct GclessAllocator {
    allocations: Arc<Mutex<Vec<Box<[u8]>>>>,
}

impl GclessAllocator {
    pub fn new() -> Self {
        Self::default()
    }
}

impl GcAllocator for GclessAllocator {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize {
        super::alloc_bytes_tracked(bytes, &self.allocations)
    }

    fn collect(&self) {
        // Gcless mode - no GC in this profile.
    }
}
