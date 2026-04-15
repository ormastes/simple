//! Ctype compatibility shims.
//!
//! Some generated SMF code ends up referencing glibc-style helper symbols such
//! as `__is_alnum`. Export stable wrappers from the runtime so those relocations
//! resolve against the host `simple` process instead of depending on libc
//! internals being directly available.

#[no_mangle]
pub extern "C" fn __is_alnum(ch: i32) -> i32 {
    unsafe { libc::isalnum(ch) }
}

#[no_mangle]
pub extern "C" fn __is_alpha(ch: i32) -> i32 {
    unsafe { libc::isalpha(ch) }
}

#[no_mangle]
pub extern "C" fn __is_digit(ch: i32) -> i32 {
    unsafe { libc::isdigit(ch) }
}

#[no_mangle]
pub extern "C" fn __is_xdigit(ch: i32) -> i32 {
    unsafe { libc::isxdigit(ch) }
}

#[no_mangle]
pub extern "C" fn __is_space(ch: i32) -> i32 {
    unsafe { libc::isspace(ch) }
}

#[no_mangle]
pub extern "C" fn __is_lower(ch: i32) -> i32 {
    unsafe { libc::islower(ch) }
}

#[no_mangle]
pub extern "C" fn __is_upper(ch: i32) -> i32 {
    unsafe { libc::isupper(ch) }
}
