//! SHA1 hash function FFI.
//!
//! Provides cryptographic SHA1 hashing functionality for compiled Simple code.
//! SHA1 produces a 160-bit (20-byte) hash value.
//!
//! **Note:** SHA1 is cryptographically broken and should not be used for security purposes.
//! Use SHA256 or better for security-critical applications.

use crate::value::core::RuntimeValue;
use sha1::{Digest, Sha1};
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref SHA1_MAP: Mutex<HashMap<i64, Sha1>> = Mutex::new(HashMap::new());
}

static mut SHA1_COUNTER: i64 = 1;

/// Create new SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_new() -> i64 {
    unsafe {
        let handle = SHA1_COUNTER;
        SHA1_COUNTER += 1;
        let hasher = Sha1::new();
        SHA1_MAP.lock().unwrap().insert(handle, hasher);
        handle
    }
}

/// Write bytes to SHA1 hasher
///
/// # Safety
/// data_ptr must be valid for data_len bytes or null
#[no_mangle]
pub unsafe extern "C" fn rt_sha1_write(handle: i64, data_ptr: *const u8, data_len: u64) {
    if data_ptr.is_null() {
        return;
    }
    let mut map = SHA1_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
        hasher.update(data);
    }
}

/// Finalize SHA1 and get hex string
#[no_mangle]
pub extern "C" fn rt_sha1_finish(handle: i64) -> RuntimeValue {
    let mut map = SHA1_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        let hex = format!("{:x}", result);
        let bytes = hex.as_bytes();
        unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

/// Finalize SHA1 and get raw bytes
#[no_mangle]
pub extern "C" fn rt_sha1_finish_bytes(handle: i64) -> RuntimeValue {
    let mut map = SHA1_MAP.lock().unwrap();
    if let Some(hasher) = map.remove(&handle) {
        let result = hasher.finalize();
        let bytes = result.as_slice();
        unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
    } else {
        RuntimeValue::NIL
    }
}

/// Reset SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_reset(handle: i64) {
    let mut map = SHA1_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        *hasher = Sha1::new();
    }
}

/// Free SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_free(handle: i64) {
    SHA1_MAP.lock().unwrap().remove(&handle);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_string_data;

    #[test]
    fn test_sha1_basic() {
        let handle = rt_sha1_new();
        assert!(handle > 0);

        // Hash "hello"
        let data = b"hello";
        unsafe {
            rt_sha1_write(handle, data.as_ptr(), data.len() as u64);
        }

        let result = rt_sha1_finish(handle);
        assert!(!result.is_nil());

        // Verify the hash is correct (SHA1 of "hello")
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d");
    }

    #[test]
    fn test_sha1_empty_string() {
        let handle = rt_sha1_new();

        let result = rt_sha1_finish(handle);
        assert!(!result.is_nil());

        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        // SHA1 of empty string
        assert_eq!(hash_str, "da39a3ee5e6b4b0d3255bfef95601890afd80709");
    }

    #[test]
    fn test_sha1_multiple_writes() {
        let handle = rt_sha1_new();

        // Write "hel" then "lo"
        unsafe {
            rt_sha1_write(handle, b"hel".as_ptr(), 3);
            rt_sha1_write(handle, b"lo".as_ptr(), 2);
        }

        let result = rt_sha1_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        // Should be same as hashing "hello" at once
        assert_eq!(hash_str, "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d");
    }

    #[test]
    fn test_sha1_reset() {
        let handle = rt_sha1_new();

        // Hash something
        unsafe {
            rt_sha1_write(handle, b"wrong".as_ptr(), 5);
        }

        // Reset and hash the correct data
        rt_sha1_reset(handle);
        unsafe {
            rt_sha1_write(handle, b"hello".as_ptr(), 5);
        }

        let result = rt_sha1_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d");
    }

    #[test]
    fn test_sha1_finish_bytes() {
        let handle = rt_sha1_new();

        unsafe {
            rt_sha1_write(handle, b"hello".as_ptr(), 5);
        }

        let result = rt_sha1_finish_bytes(handle);
        assert!(!result.is_nil());

        // Raw bytes should be 20 bytes (160 bits)
        let len = crate::value::collections::rt_string_len(result);
        assert_eq!(len, 20);
    }

    #[test]
    fn test_sha1_null_data() {
        let handle = rt_sha1_new();

        // Writing null data should be safe
        unsafe {
            rt_sha1_write(handle, std::ptr::null(), 100);
        }

        // Should get empty string hash
        let result = rt_sha1_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "da39a3ee5e6b4b0d3255bfef95601890afd80709");
    }

    #[test]
    fn test_sha1_invalid_handle() {
        // Finish with invalid handle
        let result = rt_sha1_finish(999999);
        assert!(result.is_nil());

        // Reset invalid handle (should not crash)
        rt_sha1_reset(999999);

        // Free invalid handle (should not crash)
        rt_sha1_free(999999);
    }

    #[test]
    fn test_sha1_double_free() {
        let handle = rt_sha1_new();
        rt_sha1_free(handle);
        // Double free should be safe
        rt_sha1_free(handle);
    }
}
