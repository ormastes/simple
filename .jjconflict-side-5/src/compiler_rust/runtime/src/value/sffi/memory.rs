//! Memory SFFI — most implementations now live in src/runtime/runtime_memory.c.
//! rt_ptr_to_value/rt_value_to_ptr stay in Rust (RuntimeValue internals).

use crate::value::core::RuntimeValue;
use crate::value::heap::HeapHeader;

mod c_sffi {
    extern "C" {
        pub(super) fn rt_alloc(size: u64) -> *mut u8;
        pub(super) fn rt_free(ptr: *mut u8, size: u64);
        pub(super) fn rt_ptr_read_i64(addr: i64, offset: i64) -> i64;
        pub(super) fn rt_ptr_read_i32(addr: i64, offset: i64) -> i32;
        pub(super) fn rt_ptr_write_u8(addr: i64, offset: i64, value: i64);
        pub(super) fn rt_ptr_write_i32(addr: i64, offset: i64, value: i32);
        pub(super) fn rt_ptr_write_i64(addr: i64, offset: i64, value: i64);
        pub(super) fn spl_f64_to_bits(value: f64) -> i64;
        pub(super) fn spl_i64_is_zero(value: i64) -> i32;
        pub(super) fn rt_memset(dst: *mut u8, val: i8, n: i64) -> *mut u8;
        pub(super) fn rt_memcpy(dst: *mut u8, src: *const u8, n: i64) -> *mut u8;
    }
}

#[inline(always)]
pub fn rt_alloc(size: u64) -> *mut u8 {
    unsafe { c_sffi::rt_alloc(size) }
}
#[inline(always)]
pub fn rt_free(ptr: *mut u8, size: u64) {
    unsafe { c_sffi::rt_free(ptr, size) }
}
#[inline(always)]
pub fn rt_ptr_read_i64(addr: i64, offset: i64) -> i64 {
    unsafe { c_sffi::rt_ptr_read_i64(addr, offset) }
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
