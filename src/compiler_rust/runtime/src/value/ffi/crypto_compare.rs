//! Constant-time comparison — implementation in src/runtime/runtime_crypto.c.

use crate::value::RuntimeValue;

mod c_ffi {
    use crate::value::RuntimeValue;
    extern "C" {
        pub(super) fn rt_constant_time_compare(a: RuntimeValue, b: RuntimeValue) -> i64;
    }
}

#[inline(always)]
pub fn rt_constant_time_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    unsafe { c_ffi::rt_constant_time_compare(a, b) }
}
