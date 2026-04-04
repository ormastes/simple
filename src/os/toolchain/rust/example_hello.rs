//! Minimal Rust program for SimpleOS
//!
//! Demonstrates that Rust can compile and run on SimpleOS via the
//! custom target specification and libc shim.

#![no_std]
#![no_main]

use core::panic::PanicInfo;

extern "C" {
    fn printf(fmt: *const u8, ...) -> i32;
    fn exit(code: i32) -> !;
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        printf(b"Hello from Rust on SimpleOS!\n\0".as_ptr());
        printf(b"Rust core library working.\n\0".as_ptr());
        printf(b"TEST PASSED\n\0".as_ptr());
    }
    0
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe {
        printf(b"PANIC: Rust panic handler invoked\n\0".as_ptr());
        exit(1);
    }
}

#[no_mangle]
pub extern "C" fn __rust_alloc(size: usize, _align: usize) -> *mut u8 {
    extern "C" {
        fn malloc(size: usize) -> *mut u8;
    }
    unsafe { malloc(size) }
}

#[no_mangle]
pub extern "C" fn __rust_dealloc(_ptr: *mut u8, _size: usize, _align: usize) {
    /* Bump allocator -- no-op free */
}

#[no_mangle]
pub extern "C" fn __rust_realloc(
    ptr: *mut u8,
    _old_size: usize,
    _align: usize,
    new_size: usize,
) -> *mut u8 {
    extern "C" {
        fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
    }
    unsafe { realloc(ptr, new_size) }
}

#[no_mangle]
pub extern "C" fn __rust_alloc_zeroed(size: usize, _align: usize) -> *mut u8 {
    extern "C" {
        fn calloc(nmemb: usize, size: usize) -> *mut u8;
    }
    unsafe { calloc(1, size) }
}
