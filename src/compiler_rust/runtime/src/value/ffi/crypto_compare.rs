//! Constant-time comparison for cryptographic use.

use crate::value::RuntimeValue;

fn runtime_text_ptr_len(v: RuntimeValue) -> Option<(i64, i64)> {
    let ptr = crate::value::collections::rt_string_data(v);
    if ptr.is_null() {
        return None;
    }
    let len = crate::value::collections::rt_string_len(v);
    if len < 0 {
        return None;
    }
    Some((ptr as i64, len))
}

/// Constant-time comparison of two text values.
/// Returns 1 if equal, 0 if not equal or on error.
/// Uses XOR accumulator — no early exit, always processes all bytes.
#[no_mangle]
pub extern "C" fn rt_constant_time_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    let Some((a_ptr, a_len)) = runtime_text_ptr_len(a) else {
        return 0;
    };
    let Some((b_ptr, b_len)) = runtime_text_ptr_len(b) else {
        return 0;
    };

    if a_len != b_len {
        return 0;
    }
    if a_len == 0 {
        return 1;
    }

    let a_slice = unsafe { std::slice::from_raw_parts(a_ptr as *const u8, a_len as usize) };
    let b_slice = unsafe { std::slice::from_raw_parts(b_ptr as *const u8, b_len as usize) };

    let mut acc: u8 = 0;
    for i in 0..a_slice.len() {
        acc |= a_slice[i] ^ b_slice[i];
    }

    if acc == 0 {
        1
    } else {
        0
    }
}
