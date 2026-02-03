// NoGC allocator stub for compatibility
//
// The actual GC implementation has been migrated to Simple (src/app/gc/)
// This is a minimal stub to maintain API compatibility.

use std::sync::Mutex;
use simple_common::gc::{GcAllocator, MemoryLimitConfig};

/// A no-GC allocator that tracks allocations but doesn't collect
pub struct NoGcAllocator {
    allocations: Mutex<Vec<Box<[u8]>>>,
    limit: usize,
}

impl NoGcAllocator {
    /// Create a new NoGcAllocator
    pub fn new() -> Self {
        Self {
            allocations: Mutex::new(Vec::new()),
            limit: 512 * 1024 * 1024,
        }
    }

    /// Create with memory limit
    pub fn with_memory_limit(limit: usize) -> Self {
        Self {
            allocations: Mutex::new(Vec::new()),
            limit,
        }
    }

    /// Create with memory config
    pub fn with_memory_config(config: MemoryLimitConfig) -> Self {
        Self::with_memory_limit(config.limit_bytes)
    }

    /// Get the count of allocations
    pub fn allocation_count(&self) -> usize {
        self.allocations.lock().unwrap().len()
    }
}

impl GcAllocator for NoGcAllocator {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize {
        super::alloc_bytes_tracked(bytes, &self.allocations)
    }

    fn allocation_count(&self) -> usize {
        self.allocations.lock().unwrap().len()
    }

    fn memory_usage(&self) -> usize {
        0 // Stub implementation
    }

    fn memory_limit(&self) -> usize {
        self.limit
    }

    fn collect(&self) -> usize {
        0 // No-op: no GC
    }
}

impl Default for NoGcAllocator {
    fn default() -> Self {
        Self::new()
    }
}
