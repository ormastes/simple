//! Rust Global Allocator Bridge for Simple Memory Tracking
//!
//! When linked into a Rust crate used via FFI, this overrides the global
//! allocator so that every Rust allocation/deallocation is routed through
//! `spl_memtrack_record` / `spl_memtrack_unrecord`.
//!
//! Build as a staticlib and link when Rust FFI crates are used.
//! Controlled by a build flag — not linked by default.
//!
//! Usage:
//!   cargo build --release
//!   Link the resulting .a alongside runtime_memtrack.c

use std::alloc::{GlobalAlloc, Layout, System};

extern "C" {
    fn spl_memtrack_record(ptr: *mut u8, size: i64, tag: *const u8);
    fn spl_memtrack_unrecord(ptr: *mut u8);
    static g_memtrack_enabled: i32;
}

/// Check if memtrack is enabled (avoids FFI call overhead)
#[inline]
fn is_tracking_enabled() -> bool {
    unsafe { g_memtrack_enabled != 0 }
}

/// Tag string for all Rust allocations (null-terminated)
static RUST_TAG: &[u8] = b"rust\0";

struct SplTrackingAllocator;

unsafe impl GlobalAlloc for SplTrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() && is_tracking_enabled() {
            unsafe {
                spl_memtrack_record(ptr, layout.size() as i64, RUST_TAG.as_ptr());
            }
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if is_tracking_enabled() {
            unsafe {
                spl_memtrack_unrecord(ptr);
            }
        }
        unsafe { System.dealloc(ptr, layout) };
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() && is_tracking_enabled() {
            unsafe {
                spl_memtrack_record(ptr, layout.size() as i64, RUST_TAG.as_ptr());
            }
        }
        ptr
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if is_tracking_enabled() {
            unsafe {
                spl_memtrack_unrecord(ptr);
            }
        }
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() && is_tracking_enabled() {
            unsafe {
                spl_memtrack_record(new_ptr, new_size as i64, RUST_TAG.as_ptr());
            }
        }
        new_ptr
    }
}

#[global_allocator]
static ALLOC: SplTrackingAllocator = SplTrackingAllocator;
