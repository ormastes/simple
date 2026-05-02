//! Global allocator backed by libsimpleos_c `malloc` / `free` / `realloc`.

use crate::alloc::{GlobalAlloc, Layout, System};
use core::ffi::c_void;
use core::ptr;

unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
    fn realloc(ptr: *mut c_void, new_size: usize) -> *mut c_void;
    fn calloc(nmemb: usize, size: usize) -> *mut c_void;
}

unsafe impl GlobalAlloc for System {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // libsimpleos_c `malloc` guarantees `max_align_t` alignment only; if a
        // caller asks for more we fall back to the usual over-allocate trick.
        if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
            unsafe { malloc(layout.size()) as *mut u8 }
        } else {
            unsafe { aligned_malloc(&layout) }
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if layout.align() <= MIN_ALIGN && layout.align() <= layout.size() {
            unsafe { calloc(layout.size(), 1) as *mut u8 }
        } else {
            let ptr = unsafe { self.alloc(layout) };
            if !ptr.is_null() {
                unsafe { ptr::write_bytes(ptr, 0, layout.size()) };
            }
            ptr
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        unsafe { free(ptr as *mut c_void) }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if layout.align() <= MIN_ALIGN && layout.align() <= new_size {
            unsafe { realloc(ptr as *mut c_void, new_size) as *mut u8 }
        } else {
            realloc_fallback(self, ptr, layout, new_size)
        }
    }
}

// 16 matches glibc's `max_align_t` for every target we ship (x86_64, aarch64,
// riscv64gc, riscv32imac). Keep in lockstep with libsimpleos_c.
#[cfg(target_pointer_width = "64")]
const MIN_ALIGN: usize = 16;
#[cfg(target_pointer_width = "32")]
const MIN_ALIGN: usize = 8;

unsafe fn aligned_malloc(layout: &Layout) -> *mut u8 {
    // Over-allocate, then round up and stash the base pointer just below the
    // returned pointer so `dealloc`/`realloc` can recover it.
    let size = layout.size() + layout.align();
    let base = unsafe { malloc(size) as *mut u8 };
    if base.is_null() {
        return ptr::null_mut();
    }
    let aligned = ((base as usize + layout.align()) & !(layout.align() - 1)) as *mut u8;
    unsafe { (aligned as *mut *mut u8).offset(-1).write(base) };
    aligned
}

fn realloc_fallback(alloc: &System, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    // SAFETY: caller guarantees `ptr`/`layout` pair is valid.
    unsafe {
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        let new_ptr = alloc.alloc(new_layout);
        if !new_ptr.is_null() {
            let copy = crate::cmp::min(layout.size(), new_size);
            ptr::copy_nonoverlapping(ptr, new_ptr, copy);
            alloc.dealloc(ptr, layout);
        }
        new_ptr
    }
}
