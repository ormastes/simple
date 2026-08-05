//! SHA256 hash function SFFI.
//!
//! Provides cryptographic SHA256 hashing functionality for compiled Simple code.
//! SHA256 produces a 256-bit (32-byte) hash value.

use crate::value::core::RuntimeValue;

use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref SHA256_MAP: Mutex<HashMap<i64, Sha256>> = Mutex::new(HashMap::new());
}

static SHA256_COUNTER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

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
    let array = crate::value::collections::rt_byte_array_new_len(bytes.len() as u64);
    if array.is_nil() {
        return RuntimeValue::NIL;
    }
    for (i, byte) in bytes.iter().enumerate() {
        let ok = crate::value::collections::rt_bytes_u8_set(array, i as i64, *byte as i64);
        if !ok {
            return RuntimeValue::NIL;
        }
    }
    array
}

#[no_mangle]
pub extern "C" fn rt_sha256_new() -> i64 {
    let handle = SHA256_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    SHA256_MAP.lock().unwrap().insert(handle, Sha256::new());
    handle
}

#[no_mangle]
pub unsafe extern "C" fn rt_sha256_write(handle: i64, data_ptr: *const u8, data_len: u64) {
    if data_ptr.is_null() {
        return;
    }
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
        hasher.update(data);
    }
}

#[no_mangle]
pub extern "C" fn rt_sha256_finish(handle: i64) -> RuntimeValue {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        let hex = format!("{:x}", result);
        unsafe { crate::value::collections::rt_string_new(hex.as_ptr(), hex.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

#[no_mangle]
pub extern "C" fn rt_sha256_finish_bytes(handle: i64) -> RuntimeValue {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        unsafe { crate::value::collections::rt_string_new(result.as_ptr(), result.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

#[no_mangle]
pub extern "C" fn rt_sha256_reset(handle: i64) {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        *hasher = Sha256::new();
    }
}

#[no_mangle]
pub extern "C" fn rt_sha256_free(handle: i64) {
    SHA256_MAP.lock().unwrap().remove(&handle);
}

pub fn clear_sha256_registry() {
    SHA256_MAP.lock().unwrap().clear();
}

#[no_mangle]
pub extern "C" fn rt_tls13_sha256(data: RuntimeValue) -> RuntimeValue {
    let Some(bytes) = runtime_byte_array_to_vec(data) else {
        return RuntimeValue::NIL;
    };
    let digest = Sha256::digest(&bytes);
    vec_to_runtime_byte_array(digest.as_slice())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_string_data;

    #[test]
    fn test_sha256_basic() {
        let handle = rt_sha256_new();
        assert!(handle > 0);

        unsafe {
            rt_sha256_write(handle, b"hello".as_ptr(), 5);
        }

        let result = rt_sha256_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(
            hash_str,
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }

    #[test]
    fn test_rt_tls13_sha256_basic() {
        let input = b"hello";
        let input_arr = crate::value::collections::rt_byte_array_new_len(input.len() as u64);
        for (i, b) in input.iter().enumerate() {
            assert!(
                crate::value::collections::rt_bytes_u8_set(input_arr, i as i64, i64::from(*b)),
                "failed to set input byte"
            );
        }

        assert_eq!(crate::value::collections::rt_array_len(input_arr), 5);
        let first = crate::value::collections::rt_array_get(input_arr, 0);
        assert!(first.is_int());
        assert_eq!(first.as_int(), 104);
        assert!(runtime_byte_array_to_vec(input_arr).is_some());
        assert_eq!(runtime_byte_array_to_vec(input_arr).unwrap(), input.to_vec());

        let result = rt_tls13_sha256(input_arr);
        assert!(!result.is_nil(), "rt_tls13_sha256 returned nil");
        let mut got = Vec::with_capacity(crate::value::collections::rt_array_len(result) as usize);
        let len = crate::value::collections::rt_array_len(result);
        for i in 0..len {
            let value = crate::value::collections::rt_array_get(result, i);
            assert!(value.is_int(), "non-int output");
            let byte = value.as_int();
            assert!((0..=255).contains(&byte));
            got.push(byte as u8);
        }
        assert_eq!(
            got.iter().map(|b| format!("{:02x}", b)).collect::<String>(),
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }
}
