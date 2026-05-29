//! Constant-time comparison.

use crate::value::collections::{rt_string_data, rt_string_len};
use crate::value::{HeapObjectType, RuntimeValue};

#[inline(always)]
pub fn rt_constant_time_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    if a.heap_type() != Some(HeapObjectType::String) || b.heap_type() != Some(HeapObjectType::String) {
        return 0;
    }
    let left_len = rt_string_len(a);
    let right_len = rt_string_len(b);
    if left_len != right_len {
        return 0;
    }
    let left_ptr = rt_string_data(a);
    let right_ptr = rt_string_data(b);
    if left_len > 0 && (left_ptr.is_null() || right_ptr.is_null()) {
        return 0;
    }
    let left = unsafe { std::slice::from_raw_parts(left_ptr as *const u8, left_len as usize) };
    let right = unsafe { std::slice::from_raw_parts(right_ptr as *const u8, right_len as usize) };
    let mut acc = 0u8;
    for i in 0..left.len() {
        acc |= left[i] ^ right[i];
    }
    if acc == 0 {
        1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_string_new;

    fn text(value: &str) -> RuntimeValue {
        unsafe { rt_string_new(value.as_ptr(), value.len() as u64) }
    }

    #[test]
    fn equal_strings_return_one() {
        assert_eq!(rt_constant_time_compare(text("abcdef"), text("abcdef")), 1);
    }

    #[test]
    fn different_strings_return_zero() {
        assert_eq!(rt_constant_time_compare(text("abcdef"), text("abcdeg")), 0);
    }

    #[test]
    fn length_mismatch_returns_zero() {
        assert_eq!(rt_constant_time_compare(text("abcdef"), text("abc")), 0);
    }
}
