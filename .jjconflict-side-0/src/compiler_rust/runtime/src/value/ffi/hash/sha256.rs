//! SHA256 hash function FFI.
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
}
