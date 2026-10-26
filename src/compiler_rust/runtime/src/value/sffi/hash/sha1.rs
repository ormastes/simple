//! SHA1 hash function SFFI.
//!
//! Provides cryptographic SHA1 hashing functionality for compiled Simple code.
//! SHA1 produces a 160-bit (20-byte) hash value.
//!
//! **Note:** SHA1 is cryptographically broken and should not be used for security purposes.
//! Use SHA256 or better for security-critical applications.

use crate::value::core::RuntimeValue;

#[cfg(feature = "runtime-sha")]
use sha1::{Digest, Sha1};
#[cfg(feature = "runtime-sha")]
use std::collections::HashMap;
#[cfg(feature = "runtime-sha")]
use std::sync::Mutex;

#[cfg(feature = "runtime-sha")]
lazy_static::lazy_static! {
    static ref SHA1_MAP: Mutex<HashMap<i64, Sha1>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "runtime-sha")]
static SHA1_COUNTER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

fn runtime_sha_unavailable(name: &str) {
    eprintln!("Runtime error: {name} is unavailable in this runtime build (enable Cargo feature `runtime-sha`)");
}

#[cfg(feature = "runtime-sha")]
fn digest_to_runtime_byte_array(bytes: &[u8]) -> RuntimeValue {
    let array = crate::value::collections::rt_byte_array_new_len(bytes.len() as u64);
    if array.is_nil() {
        return RuntimeValue::NIL;
    }
    if !crate::value::byte_array_write(array, bytes) {
        return RuntimeValue::NIL;
    }
    array
}

/// Create new SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_new() -> i64 {
    #[cfg(not(feature = "runtime-sha"))]
    {
        runtime_sha_unavailable("rt_sha1_new");
        -1
    }

    #[cfg(feature = "runtime-sha")]
    {
        let handle = SHA1_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
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
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
        let _ = data_ptr;
        let _ = data_len;
        runtime_sha_unavailable("rt_sha1_write");
    }

    #[cfg(feature = "runtime-sha")]
    {
        if data_ptr.is_null() {
            return;
        }
        let Ok(data_len) = usize::try_from(data_len) else {
            return;
        };
        let mut map = SHA1_MAP.lock().unwrap();
        if let Some(hasher) = map.get_mut(&handle) {
            let data = std::slice::from_raw_parts(data_ptr, data_len);
            hasher.update(data);
        }
    }
}

/// Finalize SHA1 and get hex string
#[no_mangle]
pub extern "C" fn rt_sha1_finish(handle: i64) -> RuntimeValue {
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
        runtime_sha_unavailable("rt_sha1_finish");
        RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR)
    }

    #[cfg(feature = "runtime-sha")]
    {
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
}

/// Finalize SHA1 and get raw bytes
#[no_mangle]
pub extern "C" fn rt_sha1_finish_bytes(handle: i64) -> RuntimeValue {
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
        runtime_sha_unavailable("rt_sha1_finish_bytes");
        RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR)
    }

    #[cfg(feature = "runtime-sha")]
    {
        let mut map = SHA1_MAP.lock().unwrap();
        if let Some(hasher) = map.remove(&handle) {
            let result = hasher.finalize();
            digest_to_runtime_byte_array(result.as_slice())
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Reset SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_reset(handle: i64) {
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
        runtime_sha_unavailable("rt_sha1_reset");
    }

    #[cfg(feature = "runtime-sha")]
    {
        let mut map = SHA1_MAP.lock().unwrap();
        if let Some(hasher) = map.get_mut(&handle) {
            *hasher = Sha1::new();
        }
    }
}

/// Free SHA1 hasher
#[no_mangle]
pub extern "C" fn rt_sha1_free(handle: i64) {
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
    }

    #[cfg(feature = "runtime-sha")]
    {
        SHA1_MAP.lock().unwrap().remove(&handle);
    }
}

/// Finalize SHA1 and get base64 string.
#[no_mangle]
pub extern "C" fn rt_sha1_finish_base64(handle: i64) -> RuntimeValue {
    #[cfg(not(feature = "runtime-sha"))]
    {
        let _ = handle;
        runtime_sha_unavailable("rt_sha1_finish_base64");
        RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR)
    }

    #[cfg(feature = "runtime-sha")]
    {
        let mut map = SHA1_MAP.lock().unwrap();
        if let Some(hasher) = map.remove(&handle) {
            let result = hasher.finalize();
            unsafe { crate::value::sffi::utils::rt_base64_encode(result.as_ptr(), result.len() as u64) }
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Clear all SHA1 hasher handles (for test cleanup)
pub fn clear_sha1_registry() {
    #[cfg(feature = "runtime-sha")]
    SHA1_MAP.lock().unwrap().clear();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::rt_string_data;

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_basic() {
        let handle = rt_sha1_new();
        assert!(handle > 0);

        let data = b"hello";
        unsafe {
            rt_sha1_write(handle, data.as_ptr(), data.len() as u64);
        }

        let result = rt_sha1_finish(handle);
        assert!(!result.is_nil());

        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d");
    }

    #[cfg(feature = "runtime-sha")]
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

        assert_eq!(hash_str, "da39a3ee5e6b4b0d3255bfef95601890afd80709");
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_multiple_writes() {
        let handle = rt_sha1_new();
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

        assert_eq!(hash_str, "aaf4c61ddcc5e8a2dabede0f3b482cd9aea9434d");
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_reset() {
        let handle = rt_sha1_new();
        unsafe {
            rt_sha1_write(handle, b"wrong".as_ptr(), 5);
        }
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

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_finish_bytes() {
        let handle = rt_sha1_new();
        unsafe {
            rt_sha1_write(handle, b"hello".as_ptr(), 5);
        }

        let result = rt_sha1_finish_bytes(handle);
        assert!(!result.is_nil());
        assert_eq!(
            crate::value::byte_array_bytes(result).unwrap(),
            [
                0xaa, 0xf4, 0xc6, 0x1d, 0xdc, 0xc5, 0xe8, 0xa2, 0xda, 0xbe, 0xd0, 0xf3, 0xb4, 0x82, 0xcd, 0x9a, 0xea,
                0x94, 0x34, 0x0d,
            ]
        );
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_null_data() {
        let handle = rt_sha1_new();
        unsafe {
            rt_sha1_write(handle, std::ptr::null(), 100);
        }

        let result = rt_sha1_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "da39a3ee5e6b4b0d3255bfef95601890afd80709");
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_invalid_handle() {
        let result = rt_sha1_finish(999999);
        assert!(result.is_nil());

        rt_sha1_reset(999999);
        rt_sha1_free(999999);
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_double_free() {
        let handle = rt_sha1_new();
        rt_sha1_free(handle);
        rt_sha1_free(handle);
    }

    #[cfg(feature = "runtime-sha")]
    #[test]
    fn test_sha1_long_input() {
        let handle = rt_sha1_new();
        let data = vec![b'a'; 1_000_000];
        unsafe {
            rt_sha1_write(handle, data.as_ptr(), data.len() as u64);
        }

        let result = rt_sha1_finish(handle);
        let hash_str = unsafe {
            let ptr = rt_string_data(result);
            let len = crate::value::collections::rt_string_len(result);
            std::str::from_utf8(std::slice::from_raw_parts(ptr, len as usize)).unwrap()
        };

        assert_eq!(hash_str, "34aa973cd4c4daa4f61eeb2bdbad27316534016f");
    }

    #[cfg(not(feature = "runtime-sha"))]
    #[test]
    fn test_sha1_stub_exports_special_error() {
        assert_eq!(rt_sha1_new(), -1);
        assert_eq!(
            rt_sha1_finish(1),
            RuntimeValue::from_special(crate::value::tags::SPECIAL_ERROR)
        );
    }
}
