//! Bulk WebSocket frame masking (RFC 6455).
//!
//! Replaces per-byte XOR masking in pure Simple with a vectorized Rust
//! implementation for the WS frame hot path.

use crate::value::RuntimeValue;

/// Bulk XOR-mask (or unmask) a byte array with a 4-byte mask key.
///
/// # Arguments
/// * `data` — RuntimeValue wrapping a `[u8]` (the payload bytes)
/// * `mask_key` — RuntimeValue wrapping a `[u8]` (exactly 4 bytes)
///
/// # Returns
/// A new `[u8]` RuntimeValue with each byte XOR'd against the rotating mask.
#[no_mangle]
pub extern "C" fn rt_ws_mask_bytes(data: RuntimeValue, mask_key: RuntimeValue) -> RuntimeValue {
    let Some(data_vec) = runtime_byte_array_to_vec(data) else {
        return crate::value::collections::rt_array_new(0);
    };
    let Some(mask_vec) = runtime_byte_array_to_vec(mask_key) else {
        return crate::value::collections::rt_array_new(0);
    };
    if mask_vec.len() != 4 {
        return crate::value::collections::rt_array_new(0);
    }

    let mask = [mask_vec[0], mask_vec[1], mask_vec[2], mask_vec[3]];
    let mut result = data_vec;

    // Process 4 bytes at a time for better throughput
    let chunks = result.len() / 4;
    for i in 0..chunks {
        let base = i * 4;
        result[base] ^= mask[0];
        result[base + 1] ^= mask[1];
        result[base + 2] ^= mask[2];
        result[base + 3] ^= mask[3];
    }
    // Handle remaining bytes
    for i in (chunks * 4)..result.len() {
        result[i] ^= mask[i % 4];
    }

    vec_to_runtime_byte_array(&result)
}

fn runtime_byte_array_to_vec(data: RuntimeValue) -> Option<Vec<u8>> {
    let len = crate::value::collections::rt_array_len(data);
    if len < 0 {
        return None;
    }
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = crate::value::collections::rt_array_get(data, i);
        if !value.is_int() {
            return None;
        }
        let byte = value.as_int();
        if !(0..=255).contains(&byte) {
            return None;
        }
        out.push(byte as u8);
    }
    Some(out)
}

fn vec_to_runtime_byte_array(bytes: &[u8]) -> RuntimeValue {
    let array = crate::value::collections::rt_array_new(bytes.len() as u64);
    for &b in bytes {
        let val = RuntimeValue::from_int(b as i64);
        crate::value::collections::rt_array_push(array, val);
    }
    array
}
