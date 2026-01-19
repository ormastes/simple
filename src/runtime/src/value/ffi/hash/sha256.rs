//! SHA256 hash function FFI.
//!
//! Provides cryptographic SHA256 hashing functionality for compiled Simple code.
//! SHA256 produces a 256-bit (32-byte) hash value and is part of the SHA-2 family.

use crate::value::core::RuntimeValue;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref SHA256_MAP: Mutex<HashMap<i64, Sha256>> = Mutex::new(HashMap::new());
}

static mut SHA256_COUNTER: i64 = 1;

/// Create new SHA256 hasher
#[no_mangle]
pub extern "C" fn rt_sha256_new() -> i64 {
    unsafe {
        let handle = SHA256_COUNTER;
        SHA256_COUNTER += 1;
        let hasher = Sha256::new();
        SHA256_MAP.lock().unwrap().insert(handle, hasher);
        handle
    }
}

/// Write bytes to SHA256 hasher
///
/// # Safety
/// data_ptr must be valid for data_len bytes or null
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

/// Finalize SHA256 and get hex string
#[no_mangle]
pub extern "C" fn rt_sha256_finish(handle: i64) -> RuntimeValue {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        let hex = format!("{:x}", result);
        let bytes = hex.as_bytes();
        unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

/// Finalize SHA256 and get raw bytes
#[no_mangle]
pub extern "C" fn rt_sha256_finish_bytes(handle: i64) -> RuntimeValue {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        let bytes = result.as_slice();
        unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

/// Reset SHA256 hasher
#[no_mangle]
pub extern "C" fn rt_sha256_reset(handle: i64) {
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        *hasher = Sha256::new();
    }
}

/// Free SHA256 hasher
#[no_mangle]
pub extern "C" fn rt_sha256_free(handle: i64) {
    SHA256_MAP.lock().unwrap().remove(&handle);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_string_data;

    #[test]
    fn test_sha256_basic() {
        let handle = rt_sha256_new();
        assert!(handle > 0);

        // Hash "hello"
        let data = b"hello";
        unsafe {
            rt_sha256_write(handle, data.as_ptr(), data.len() as u64);
        }

        let result = rt_sha256_finish(handle);
        assert!(!result.is_nil());

        // Verify the hash is correct (SHA256 of "hello")
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
    fn test_sha256_empty_string() {
        let handle = rt_sha256_new();

        let result = rt_sha256_finish(handle);
        assert!(!result.is_nil());

        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        // SHA256 of empty string
        assert_eq!(
            hash_str,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn test_sha256_multiple_writes() {
        let handle = rt_sha256_new();

        // Write "hel" then "lo"
        unsafe {
            rt_sha256_write(handle, b"hel".as_ptr(), 3);
            rt_sha256_write(handle, b"lo".as_ptr(), 2);
        }

        let result = rt_sha256_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        // Should be same as hashing "hello" at once
        assert_eq!(
            hash_str,
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }

    #[test]
    fn test_sha256_reset() {
        let handle = rt_sha256_new();

        // Hash something
        unsafe {
            rt_sha256_write(handle, b"wrong".as_ptr(), 5);
        }

        // Reset and hash the correct data
        rt_sha256_reset(handle);
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
    fn test_sha256_finish_bytes() {
        let handle = rt_sha256_new();

        unsafe {
            rt_sha256_write(handle, b"hello".as_ptr(), 5);
        }

        let result = rt_sha256_finish_bytes(handle);
        assert!(!result.is_nil());

        // Raw bytes should be 32 bytes (256 bits)
        let len = crate::value::collections::rt_string_len(result);
        assert_eq!(len, 32);
    }

    #[test]
    fn test_sha256_null_data() {
        let handle = rt_sha256_new();

        // Writing null data should be safe
        unsafe {
            rt_sha256_write(handle, std::ptr::null(), 100);
        }

        // Should get empty string hash
        let result = rt_sha256_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(
            hash_str,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn test_sha256_invalid_handle() {
        // Finish with invalid handle
        let result = rt_sha256_finish(999999);
        assert!(result.is_nil());

        // Reset invalid handle (should not crash)
        rt_sha256_reset(999999);

        // Free invalid handle (should not crash)
        rt_sha256_free(999999);
    }

    #[test]
    fn test_sha256_double_free() {
        let handle = rt_sha256_new();
        rt_sha256_free(handle);
        // Double free should be safe
        rt_sha256_free(handle);
    }

    #[test]
    fn test_sha256_long_input() {
        let handle = rt_sha256_new();

        // Hash a longer input
        let data = b"The quick brown fox jumps over the lazy dog";
        unsafe {
            rt_sha256_write(handle, data.as_ptr(), data.len() as u64);
        }

        let result = rt_sha256_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(
            hash_str,
            "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"
        );
    }
}
