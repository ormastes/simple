// GC stub module for compatibility
//
// The actual GC implementation has been migrated to Simple (src/app/gc/)
// These are minimal stubs to maintain API compatibility with existing code.

use std::sync::atomic::{AtomicUsize, Ordering};

static UNIQUE_ROOT_COUNT: AtomicUsize = AtomicUsize::new(0);
static SHARED_ROOT_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Register a unique root with the GC (stub - no-op)
/// Accepts any pointer type via cast
#[inline]
pub fn register_unique_root<T>(_ptr: *const T) {
    UNIQUE_ROOT_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Unregister a unique root from the GC (stub - no-op)
/// Accepts any pointer type via cast
#[inline]
pub fn unregister_unique_root<T>(_ptr: *const T) {
    UNIQUE_ROOT_COUNT.fetch_sub(1, Ordering::Relaxed);
}

/// Register a shared root with the GC (stub - no-op)
/// Accepts any pointer type via cast
#[inline]
pub fn register_shared_root<T>(_ptr: *const T) {
    SHARED_ROOT_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// Unregister a shared root from the GC (stub - no-op)
/// Accepts any pointer type via cast
#[inline]
pub fn unregister_shared_root<T>(_ptr: *const T) {
    SHARED_ROOT_COUNT.fetch_sub(1, Ordering::Relaxed);
}

/// Get count of unique roots (for testing)
#[inline]
pub fn unique_root_count() -> usize {
    UNIQUE_ROOT_COUNT.load(Ordering::Relaxed)
}

/// Get count of shared roots (for testing)
#[inline]
pub fn shared_root_count() -> usize {
    SHARED_ROOT_COUNT.load(Ordering::Relaxed)
}

use simple_common::gc::GcAllocator;
pub use simple_common::gc::GcOptions;

/// GC runtime stub for compatibility
pub struct GcRuntime {
    limit: usize,
}

impl GcRuntime {
    pub fn new() -> Self {
        Self {
            limit: 512 * 1024 * 1024,
        }
    }

    pub fn with_memory_limit(limit: usize) -> Self {
        Self { limit }
    }

    pub fn with_memory_limit_mb(mb: usize) -> Self {
        Self {
            limit: mb * 1024 * 1024,
        }
    }

    pub fn with_memory_limit_gb(gb: usize) -> Self {
        Self {
            limit: gb * 1024 * 1024 * 1024,
        }
    }

    pub fn with_options(_opts: GcOptions, _provider: Option<()>, config: simple_common::gc::MemoryLimitConfig) -> Self {
        Self {
            limit: config.limit_bytes,
        }
    }

    pub fn unlimited() -> Self {
        Self { limit: usize::MAX }
    }

    pub fn verbose_stdout() -> Self {
        Self::new()
    }

    pub fn memory_usage(&self) -> usize {
        0
    }

    pub fn memory_limit(&self) -> usize {
        self.limit
    }

    pub fn collect(&self, _reason: &str) -> usize {
        0 // Stub: GC is in Simple now
    }
}

impl GcAllocator for GcRuntime {
    fn alloc_bytes(&self, _bytes: &[u8]) -> usize {
        0
    }

    fn allocation_count(&self) -> usize {
        0
    }

    fn memory_usage(&self) -> usize {
        0
    }

    fn memory_limit(&self) -> usize {
        self.limit
    }

    fn collect(&self) -> usize {
        0 // Stub: GC is in Simple
    }
}

impl Default for GcRuntime {
    fn default() -> Self {
        Self::new()
    }
}
