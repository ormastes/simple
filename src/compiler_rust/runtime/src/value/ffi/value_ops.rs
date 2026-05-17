//! Value creation, extraction, and type checking — implementations in src/runtime/runtime_value.c.

use crate::value::core::RuntimeValue;

mod c_ffi {
    use crate::value::core::RuntimeValue;
    extern "C" {
        pub(super) fn rt_value_int(i: i64) -> RuntimeValue;
        pub(super) fn rt_value_float(f: f64) -> RuntimeValue;
        pub(super) fn rt_value_bool(b: bool) -> RuntimeValue;
        pub(super) fn rt_value_nil() -> RuntimeValue;
        pub(super) fn rt_value_as_int(v: RuntimeValue) -> i64;
        pub(super) fn rt_value_as_float(v: RuntimeValue) -> f64;
        pub(super) fn rt_value_as_bool(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_truthy(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_is_nil(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_is_int(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_is_float(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_is_bool(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_is_heap(v: RuntimeValue) -> bool;
        pub(super) fn rt_value_type_tag(v: RuntimeValue) -> u8;
        pub(super) fn rt_is_error(v: RuntimeValue) -> bool;
    }
}

#[inline(always)]
pub fn rt_value_int(i: i64) -> RuntimeValue { unsafe { c_ffi::rt_value_int(i) } }
#[inline(always)]
pub fn rt_value_float(f: f64) -> RuntimeValue { unsafe { c_ffi::rt_value_float(f) } }
#[inline(always)]
pub fn rt_value_bool(b: bool) -> RuntimeValue { unsafe { c_ffi::rt_value_bool(b) } }
#[inline(always)]
pub fn rt_value_nil() -> RuntimeValue { unsafe { c_ffi::rt_value_nil() } }
#[inline(always)]
pub fn rt_value_as_int(v: RuntimeValue) -> i64 { unsafe { c_ffi::rt_value_as_int(v) } }
#[inline(always)]
pub fn rt_value_as_float(v: RuntimeValue) -> f64 { unsafe { c_ffi::rt_value_as_float(v) } }
#[inline(always)]
pub fn rt_value_as_bool(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_as_bool(v) } }
#[inline(always)]
pub fn rt_value_truthy(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_truthy(v) } }
#[inline(always)]
pub fn rt_value_is_nil(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_is_nil(v) } }
#[inline(always)]
pub fn rt_value_is_int(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_is_int(v) } }
#[inline(always)]
pub fn rt_value_is_float(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_is_float(v) } }
#[inline(always)]
pub fn rt_value_is_bool(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_is_bool(v) } }
#[inline(always)]
pub fn rt_value_is_heap(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_value_is_heap(v) } }
#[inline(always)]
pub fn rt_value_type_tag(v: RuntimeValue) -> u8 { unsafe { c_ffi::rt_value_type_tag(v) } }
#[inline(always)]
pub fn rt_is_error(v: RuntimeValue) -> bool { unsafe { c_ffi::rt_is_error(v) } }
