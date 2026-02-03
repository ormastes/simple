// GC constants and stub types for compatibility
//
// The actual GC implementation has been migrated to Simple (src/app/gc/)
// This module provides minimal stubs for compatibility.

/// Default memory limit (512 MB)
pub const DEFAULT_MEMORY_LIMIT: usize = 512 * 1024 * 1024;

/// GC allocator trait for compatibility
pub trait GcAllocator: Send + Sync {
    /// Allocate bytes and return pointer
    fn alloc_bytes(&self, bytes: &[u8]) -> usize;

    /// Get allocation count
    fn allocation_count(&self) -> usize;

    /// Get current memory usage (stub)
    fn memory_usage(&self) -> usize {
        0
    }

    /// Get memory limit (stub)
    fn memory_limit(&self) -> usize {
        DEFAULT_MEMORY_LIMIT
    }

    /// Collect garbage (stub)
    fn collect(&self) -> usize {
        0
    }
}

/// Memory limit configuration (stub)
#[derive(Clone, Debug)]
pub struct MemoryLimitConfig {
    pub limit_bytes: usize,
    pub fail_on_exceeded: bool,
}

impl MemoryLimitConfig {
    pub fn new(limit: usize) -> Self {
        Self {
            limit_bytes: limit,
            fail_on_exceeded: false,
        }
    }

    pub fn unlimited() -> Self {
        Self {
            limit_bytes: usize::MAX,
            fail_on_exceeded: false,
        }
    }

    pub fn limit(&self) -> usize {
        self.limit_bytes
    }
}

impl Default for MemoryLimitConfig {
    fn default() -> Self {
        Self {
            limit_bytes: DEFAULT_MEMORY_LIMIT,
            fail_on_exceeded: false,
        }
    }
}

/// GC options (stub)
#[derive(Clone, Debug, Default)]
pub struct GcOptions {
    pub memory_limit: Option<usize>,
}

impl GcOptions {
    pub fn new() -> Self {
        Self { memory_limit: None }
    }
}
