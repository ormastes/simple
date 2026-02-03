//! gc module
//!
//! Garbage Collector FFI
//! 
//! Uses Boehm-Demers-Weiser GC (bdwgc) as the garbage collector.
//! This is a conservative, portable GC used by many language runtimes.

use std::alloc::{GlobalAlloc, Layout};

// ==============================================================================
// FFI Functions
// ==============================================================================

/// Initialize the GC
#[no_mangle]
pub extern "C" fn rt_gc_init() {
    // bdwgc initializes automatically on first allocation
    // This is a no-op but kept for API compatibility
}

/// Allocate memory (GC-managed)
#[no_mangle]
pub unsafe extern "C" fn rt_gc_malloc(size: usize) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }

    let layout = Layout::from_size_align_unchecked(size, 8);
    bdwgc_alloc::Allocator.alloc(layout)
}

/// Allocate atomic memory (no pointers, won't be scanned)
#[no_mangle]
pub unsafe extern "C" fn rt_gc_malloc_atomic(size: usize) -> *mut u8 {
    // For now, use same as regular malloc
    // bdwgc has atomic allocation but not exposed in bdwgc-alloc crate yet
    rt_gc_malloc(size)
}

/// Force garbage collection
#[no_mangle]
pub extern "C" fn rt_gc_collect() {
    // bdwgc-alloc doesn't expose explicit collection
    // Collection happens automatically
}

/// Get heap size
#[no_mangle]
pub extern "C" fn rt_gc_get_heap_size() -> usize {
    // Not available in bdwgc-alloc
    0
}

/// Get free bytes
#[no_mangle]
pub extern "C" fn rt_gc_get_free_bytes() -> usize {
    // Not available in bdwgc-alloc
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "TODO: bdwgc has issues in test environment - test in integration tests instead"]
    fn test_gc_malloc() {
        rt_gc_init();
        unsafe {
            let ptr = rt_gc_malloc(1024);
            assert!(!ptr.is_null());
            // Write some data
            *ptr = 42;
            assert_eq!(*ptr, 42);
        }
    }

    #[test]
    #[ignore = "TODO: bdwgc has issues in test environment - test in integration tests instead"]
    fn test_gc_malloc_atomic() {
        unsafe {
            let ptr = rt_gc_malloc_atomic(512);
            assert!(!ptr.is_null());
        }
    }

}
