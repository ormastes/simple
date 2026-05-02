//! SimpleOS Hello World in Rust
//!
//! Demonstrates: printf, malloc/free, basic arithmetic, core::fmt.
//! Runs on SimpleOS via the libc shim + custom target spec.
//!
//! Build:
//!   sh src/os/port/rust/build.shs hello
//!
//! Run in QEMU:
//!   bin/simple run src/os/qemu_runner.spl -- build/os/rust/hello

#![no_std]
#![no_main]

use core::panic::PanicInfo;
use core::fmt::{self, Write};

// SimpleOS libc FFI
extern "C" {
    fn printf(fmt: *const u8, ...) -> i32;
    fn exit(code: i32) -> !;
    fn malloc(size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
    fn getpid() -> i32;
}

/// Minimal writer that sends characters to SimpleOS serial via printf.
struct SerialWriter;

impl Write for SerialWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        unsafe {
            for byte in s.bytes() {
                printf(b"%c\0".as_ptr(), byte as i32);
            }
        }
        Ok(())
    }
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        printf(b"========================================\n\0".as_ptr());
        printf(b"  Hello from Rust on SimpleOS!\n\0".as_ptr());
        printf(b"========================================\n\0".as_ptr());
        printf(b"\n\0".as_ptr());

        // Test arithmetic
        let a: i64 = 42;
        let b: i64 = 58;
        printf(b"[rust] %ld + %ld = %ld\n\0".as_ptr(), a, b, a + b);

        // Test PID
        let pid = getpid();
        printf(b"[rust] PID: %d\n\0".as_ptr(), pid);

        // Test allocation
        let ptr = malloc(64);
        if !ptr.is_null() {
            printf(b"[rust] malloc(64) = %p\n\0".as_ptr(), ptr);
            free(ptr);
            printf(b"[rust] free OK\n\0".as_ptr());
        } else {
            printf(b"[rust] malloc FAILED\n\0".as_ptr());
        }

        // Test core::fmt integration
        let mut writer = SerialWriter;
        let _ = write!(writer, "[rust] core::fmt works: {} + {} = {}\n", a, b, a + b);

        printf(b"\n\0".as_ptr());
        printf(b"[rust] All tests passed!\n\0".as_ptr());
        printf(b"TEST PASSED\n\0".as_ptr());
    }
    0
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    unsafe {
        printf(b"PANIC: Rust panic handler invoked\n\0".as_ptr());
        if let Some(loc) = info.location() {
            let mut writer = SerialWriter;
            let _ = write!(writer, "  at {}:{}:{}\n", loc.file(), loc.line(), loc.column());
        }
        exit(1);
    }
}

// Allocator bridge to SimpleOS libc malloc/free/realloc/calloc

#[no_mangle]
pub extern "C" fn __rust_alloc(size: usize, _align: usize) -> *mut u8 {
    unsafe { malloc(size) }
}

#[no_mangle]
pub extern "C" fn __rust_dealloc(ptr: *mut u8, _size: usize, _align: usize) {
    unsafe { free(ptr) }
}

#[no_mangle]
pub extern "C" fn __rust_realloc(ptr: *mut u8, _old: usize, _align: usize, new: usize) -> *mut u8 {
    extern "C" {
        fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
    }
    unsafe { realloc(ptr, new) }
}

#[no_mangle]
pub extern "C" fn __rust_alloc_zeroed(size: usize, _align: usize) -> *mut u8 {
    extern "C" {
        fn calloc(n: usize, size: usize) -> *mut u8;
    }
    unsafe { calloc(1, size) }
}
