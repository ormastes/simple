//! Process exit. Defers to libsimpleos_c `_exit`, which never returns.

unsafe extern "C" {
    fn _exit(status: i32) -> !;
}

pub fn exit(code: i32) -> ! {
    // SAFETY: `_exit` is a terminal syscall wrapper; it cannot return.
    unsafe { _exit(code) }
}

pub fn abort_internal() -> ! {
    exit(134)
}
