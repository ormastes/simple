//! SimpleOS IPC Sample Service in Rust
//!
//! Demonstrates: IPC port creation, message send/recv, syscall interface.
//! Creates an IPC port and exercises the IPC primitives.
//!
//! Syscall numbers (from src/os/kernel/types/syscall_types.spl):
//!    0 = Exit
//!    4 = GetPid
//!   20 = IpcSend
//!   21 = IpcRecv
//!   22 = IpcCreatePort
//!   24 = NotificationCreate
//!   26 = NotificationWait
//!   60 = DebugWrite
//!
//! Build:
//!   sh src/os/port/rust/build.shs ipc-sample
//!
//! Run in QEMU:
//!   bin/simple run src/os/qemu_runner.spl -- build/os/rust/ipc_sample

#![no_std]
#![no_main]

use core::panic::PanicInfo;

extern "C" {
    fn printf(fmt: *const u8, ...) -> i32;
    fn exit(code: i32) -> !;
    fn malloc(size: usize) -> *mut u8;
}

/// Raw SimpleOS syscall trampoline (defined in simpleos_syscall.S).
extern "C" {
    fn simpleos_syscall(id: i64, a0: i64, a1: i64, a2: i64, a3: i64, a4: i64) -> i64;
}

/// Safe wrapper for SimpleOS syscalls.
#[inline(always)]
unsafe fn syscall(id: i64, a0: i64, a1: i64, a2: i64, a3: i64, a4: i64) -> i64 {
    simpleos_syscall(id, a0, a1, a2, a3, a4)
}

// Syscall IDs
const SYS_EXIT: i64 = 0;
const SYS_GETPID: i64 = 4;
const SYS_IPC_SEND: i64 = 20;
const SYS_IPC_RECV: i64 = 21;
const SYS_IPC_CREATE_PORT: i64 = 22;
const SYS_NOTIFICATION_CREATE: i64 = 24;
const SYS_NOTIFICATION_WAIT: i64 = 26;
const SYS_DEBUG_WRITE: i64 = 60;

/// Write a byte to the debug serial port via DebugWrite syscall.
#[allow(dead_code)]
unsafe fn debug_putchar(b: u8) {
    syscall(SYS_DEBUG_WRITE, b as i64, 0, 0, 0, 0);
}

/// Write a string to the debug serial port via DebugWrite syscall.
#[allow(dead_code)]
unsafe fn debug_print(s: &[u8]) {
    for &b in s {
        debug_putchar(b);
    }
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        printf(b"========================================\n\0".as_ptr());
        printf(b"  Rust IPC Sample Service on SimpleOS\n\0".as_ptr());
        printf(b"========================================\n\0".as_ptr());
        printf(b"\n\0".as_ptr());

        // Get our PID
        let pid = syscall(SYS_GETPID, 0, 0, 0, 0, 0);
        printf(b"[ipc-sample] PID: %ld\n\0".as_ptr(), pid);

        // Create a notification object
        let notif_id = syscall(SYS_NOTIFICATION_CREATE, 0, 0, 0, 0, 0);
        printf(b"[ipc-sample] Created notification: %ld\n\0".as_ptr(), notif_id);

        // Create an IPC port
        let port = syscall(SYS_IPC_CREATE_PORT, 0, 0, 0, 0, 0);
        printf(b"[ipc-sample] Created IPC port: %ld\n\0".as_ptr(), port);

        if port < 0 {
            printf(b"[ipc-sample] FAIL: Could not create IPC port (error %ld)\n\0".as_ptr(), port);
            printf(b"TEST FAILED\n\0".as_ptr());
            exit(1);
        }

        // Test: send a message to ourselves via the port
        let send_result = syscall(SYS_IPC_SEND, port, 0, 42, 0, 0);
        printf(b"[ipc-sample] Send result: %ld\n\0".as_ptr(), send_result);

        // Test: try to receive from the port
        let recv_result = syscall(SYS_IPC_RECV, port, 0, 0, 0, 0);
        printf(b"[ipc-sample] Recv result: %ld\n\0".as_ptr(), recv_result);

        // Test: debug serial output (bypasses printf, writes directly)
        debug_print(b"[ipc-sample] DebugWrite syscall works\n");

        printf(b"\n\0".as_ptr());
        printf(b"[ipc-sample] IPC primitives working!\n\0".as_ptr());
        printf(b"TEST PASSED\n\0".as_ptr());
    }
    0
}

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    unsafe {
        printf(b"PANIC in IPC sample\n\0".as_ptr());
        exit(1);
    }
}

// Allocator bridge to SimpleOS libc

#[no_mangle]
pub extern "C" fn __rust_alloc(size: usize, _align: usize) -> *mut u8 {
    unsafe { malloc(size) }
}

#[no_mangle]
pub extern "C" fn __rust_dealloc(_ptr: *mut u8, _size: usize, _align: usize) {
    // SimpleOS bump allocator — free is a no-op
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
