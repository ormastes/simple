use std::sync::{Arc, Mutex};

use simple_common::gc::{AllocResult, GcAllocator, MemoryLimitConfig, MemoryTracker};

/// Minimal allocator that satisfies the `GcAllocator` contract without tracing.
///
/// This is the "gcless" profile: allocations are backed by boxed buffers that live
/// for the lifetime of the allocator. `collect` is a no-op.
/// Now supports configurable memory limits (default: 1 GB).
#[derive(Clone)]
pub struct GclessAllocator {
    allocations: Arc<Mutex<Vec<Box<[u8]>>>>,
    memory_tracker: Arc<MemoryTracker>,
}

impl Default for GclessAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl GclessAllocator {
    /// Create with default memory limit (1 GB)
    pub fn new() -> Self {
        Self::with_memory_config(MemoryLimitConfig::default())
    }

    /// Create with unlimited memory
    pub fn unlimited() -> Self {
        Self::with_memory_config(MemoryLimitConfig::unlimited())
    }

    /// Create with custom memory configuration
    pub fn with_memory_config(config: MemoryLimitConfig) -> Self {
        Self {
            allocations: Arc::new(Mutex::new(Vec::new())),
            memory_tracker: Arc::new(MemoryTracker::with_config(config)),
        }
    }

    /// Create with specific memory limit in bytes
    pub fn with_memory_limit(limit_bytes: usize) -> Self {
        Self::with_memory_config(MemoryLimitConfig::with_limit(limit_bytes))
    }

    /// Create with memory limit in megabytes
    pub fn with_memory_limit_mb(limit_mb: usize) -> Self {
        Self::with_memory_config(MemoryLimitConfig::with_limit_mb(limit_mb))
    }

    /// Create with memory limit in gigabytes
    pub fn with_memory_limit_gb(limit_gb: usize) -> Self {
        Self::with_memory_config(MemoryLimitConfig::with_limit_gb(limit_gb))
    }

    /// Get current memory usage in bytes
    pub fn memory_usage(&self) -> usize {
        self.memory_tracker.current_bytes()
    }

    /// Get memory limit in bytes (0 if unlimited)
    pub fn memory_limit(&self) -> usize {
        self.memory_tracker.limit_bytes()
    }
}

impl GcAllocator for GclessAllocator {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize {
        match self.try_alloc_bytes(bytes) {
            Ok(ptr) => ptr,
            Err(e) => panic!("{}", e),
        }
    }

    fn try_alloc_bytes(&self, bytes: &[u8]) -> AllocResult<usize> {
        super::alloc_bytes_tracked_with_limit(bytes, &self.allocations, &self.memory_tracker)
    }

    fn collect(&self) {
        // Gcless mode - no GC in this profile.
    }

    fn memory_usage(&self) -> usize {
        self.memory_tracker.current_bytes()
    }

    fn memory_limit(&self) -> usize {
        self.memory_tracker.limit_bytes()
    }
}
