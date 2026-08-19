//! Memory SFFI — most implementations now live in src/runtime/runtime_memory.c.
//! rt_ptr_to_value/rt_value_to_ptr stay in Rust (RuntimeValue internals).

use crate::value::core::RuntimeValue;
use crate::value::heap::HeapHeader;

mod c_sffi {
    extern "C" {
        pub(super) fn rt_alloc(size: i64) -> *mut u8;
        pub(super) fn rt_free(ptr: *mut u8);
        pub(super) fn rt_ptr_read_i64(addr: i64, offset: i64) -> i64;
        pub(super) fn rt_ptr_read_u8(addr: i64, offset: i64) -> i64;
        pub(super) fn rt_ptr_read_i32(addr: i64, offset: i64) -> i32;
        pub(super) fn rt_ptr_write_u8(addr: i64, offset: i64, value: i64);
        pub(super) fn rt_ptr_write_i32(addr: i64, offset: i64, value: i32);
        pub(super) fn rt_ptr_write_i64(addr: i64, offset: i64, value: i64);
        pub(super) fn rt_ptr_write_bytes_raw(addr: i64, offset: i64, src: *const u8, len: i64) -> i64;
        pub(super) fn spl_f64_to_bits(value: f64) -> i64;
        pub(super) fn spl_i64_is_zero(value: i64) -> i32;
        pub(super) fn rt_memset(dst: *mut u8, val: i8, n: i64) -> *mut u8;
        pub(super) fn rt_memcpy(dst: *mut u8, src: *const u8, n: i64) -> *mut u8;
    }
}

#[inline(always)]
pub fn rt_alloc(size: u64) -> *mut u8 {
    if size > i64::MAX as u64 {
        return std::ptr::null_mut();
    }
    unsafe { c_sffi::rt_alloc(size as i64) }
}
#[inline(always)]
pub fn rt_free(ptr: *mut u8) {
    unsafe { c_sffi::rt_free(ptr) }
}
#[inline(always)]
pub fn rt_ptr_read_i64(addr: i64, offset: i64) -> i64 {
    unsafe { c_sffi::rt_ptr_read_i64(addr, offset) }
}
#[inline(always)]
pub fn rt_ptr_read_u8(addr: i64, offset: i64) -> i64 {
    unsafe { c_sffi::rt_ptr_read_u8(addr, offset) }
}
#[inline(always)]
pub fn rt_ptr_read_i32(addr: i64, offset: i64) -> i32 {
    unsafe { c_sffi::rt_ptr_read_i32(addr, offset) }
}
#[inline(always)]
pub fn rt_ptr_write_u8(addr: i64, offset: i64, value: i64) {
    unsafe { c_sffi::rt_ptr_write_u8(addr, offset, value) }
}
#[inline(always)]
pub fn rt_ptr_write_i32(addr: i64, offset: i64, value: i32) {
    unsafe { c_sffi::rt_ptr_write_i32(addr, offset, value) }
}
#[inline(always)]
pub fn rt_ptr_write_i64(addr: i64, offset: i64, value: i64) {
    unsafe { c_sffi::rt_ptr_write_i64(addr, offset, value) }
}
/// All-i64 bulk copy: `memcpy(addr + offset, src, len)`.
///
/// Deliberately takes the source as a raw i64 address rather than an array
/// value: a `[u8]`-typed extern cannot be JIT-linked, so every such call is
/// routed through the JIT->interpreter bridge, which boxes the array element by
/// element (measured ~49ns/byte). All-i64 keeps the call in the JIT's direct
/// SFFI table. Pair with `rt_array_data_ptr` to obtain `src`.
// NOT #[no_mangle]: the C runtime already exports `rt_ptr_write_bytes_raw`.
// This is the Rust-side callable shim over it, kept `extern "C"` so its address
// can be handed to the JIT symbol table verbatim.
pub extern "C" fn rt_ptr_write_bytes_raw_shim(addr: i64, offset: i64, src: i64, len: i64) -> i64 {
    if addr == 0 || src == 0 || offset < 0 || len <= 0 {
        return 0;
    }
    unsafe { c_sffi::rt_ptr_write_bytes_raw(addr, offset, src as usize as *const u8, len) }
}
#[inline(always)]
pub fn spl_f64_to_bits(value: f64) -> i64 {
    unsafe { c_sffi::spl_f64_to_bits(value) }
}
#[inline(always)]
pub fn spl_i64_is_zero(value: i64) -> i32 {
    unsafe { c_sffi::spl_i64_is_zero(value) }
}
#[inline(always)]
pub fn rt_memset(dst: *mut u8, val: i8, n: i64) -> *mut u8 {
    unsafe { c_sffi::rt_memset(dst, val, n) }
}
#[inline(always)]
pub fn rt_memcpy(dst: *mut u8, src: *const u8, n: i64) -> *mut u8 {
    unsafe { c_sffi::rt_memcpy(dst, src, n) }
}

#[no_mangle]
pub extern "C" fn rt_ptr_to_value(ptr: *mut u8) -> RuntimeValue {
    if ptr.is_null() {
        RuntimeValue::NIL
    } else {
        unsafe { RuntimeValue::from_heap_ptr(ptr.cast::<HeapHeader>()) }
    }
}
#[no_mangle]
pub extern "C" fn rt_value_to_ptr(v: RuntimeValue) -> *mut u8 {
    if v.is_heap() {
        v.as_heap_ptr().cast::<u8>()
    } else {
        std::ptr::null_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rt_free_matches_one_pointer_runtime_abi_and_accepts_null() {
        let free_fn: fn(*mut u8) = rt_free;
        free_fn(std::ptr::null_mut());
    }
}
