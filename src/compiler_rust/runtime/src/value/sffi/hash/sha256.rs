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
    if !crate::value::byte_array_write(array, bytes) {
        return RuntimeValue::NIL;
    }
    array
}

#[no_mangle]
pub extern "C" fn rt_sha256_new() -> i64 {
    let Ok(handle) = SHA256_COUNTER.fetch_update(
        std::sync::atomic::Ordering::SeqCst,
        std::sync::atomic::Ordering::SeqCst,
        |current| current.checked_add(1),
    ) else {
        return -1;
    };
    SHA256_MAP.lock().unwrap().insert(handle, Sha256::new());
    handle
}

#[no_mangle]
pub unsafe extern "C" fn rt_sha256_write(handle: i64, data_ptr: *const u8, data_len: u64) {
    if data_ptr.is_null() {
        return;
    }
    let Ok(data_len) = usize::try_from(data_len) else {
        return;
    };
    let mut map = SHA256_MAP.lock().unwrap();
    if let Some(hasher) = map.get_mut(&handle) {
        let data = std::slice::from_raw_parts(data_ptr, data_len);
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
        vec_to_runtime_byte_array(result.as_slice())
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

/// Contract: `int rt_sha256_file_raw_v1(const char *path, uint8_t out[32])`
/// (`src/runtime/runtime_native.c:13186`). Reads the file at `path` and
/// writes its raw 32-byte SHA-256 digest to `out`; returns `1` on success,
/// `0` on any failure (`path` null/empty, `out` null, the file cannot be
/// opened, or a read error occurs), matching the C function's fail paths
/// exactly (`runtime_native.c:13187,13189,13206`). `path` is a C string that
/// need not be valid UTF-8 (`fopen` places no such requirement on it), so
/// this decodes it as raw bytes rather than rejecting non-UTF-8 paths the C
/// side accepts.
#[no_mangle]
pub unsafe extern "C" fn rt_sha256_file_raw_v1(
    path: *const std::os::raw::c_char,
    out: *mut u8,
) -> std::os::raw::c_int {
    if path.is_null() || out.is_null() {
        return 0;
    }
    let bytes = std::ffi::CStr::from_ptr(path).to_bytes();
    if bytes.is_empty() {
        return 0;
    }
    #[cfg(unix)]
    let path_buf: std::path::PathBuf = {
        use std::os::unix::ffi::OsStrExt;
        std::ffi::OsStr::from_bytes(bytes).into()
    };
    #[cfg(not(unix))]
    let path_buf: std::path::PathBuf = {
        let Ok(s) = std::str::from_utf8(bytes) else {
            return 0;
        };
        std::path::PathBuf::from(s)
    };

    let mut file = match std::fs::File::open(&path_buf) {
        Ok(f) => f,
        Err(_) => return 0,
    };
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 65536];
    loop {
        match std::io::Read::read(&mut file, &mut buf) {
            Ok(0) => break,
            Ok(n) => hasher.update(&buf[..n]),
            Err(_) => return 0,
        }
    }
    let digest = hasher.finalize();
    std::ptr::copy_nonoverlapping(digest.as_slice().as_ptr(), out, 32);
    1
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
    fn test_sha256_finish_bytes_is_typed_array() {
        let handle = rt_sha256_new();
        unsafe {
            rt_sha256_write(handle, b"hello".as_ptr(), 5);
        }
        let result = rt_sha256_finish_bytes(handle);
        let bytes = crate::value::byte_array_bytes(result).unwrap();
        assert_eq!(
            bytes.iter().map(|byte| format!("{byte:02x}")).collect::<String>(),
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

    fn digest_hex(out: &[u8; 32]) -> String {
        out.iter().map(|b| format!("{:02x}", b)).collect()
    }

    #[test]
    fn test_rt_sha256_file_raw_v1_known_vector() {
        let dir = std::env::temp_dir();
        let path = dir.join(format!("rt_sha256_file_raw_v1_test_{}.txt", std::process::id()));
        std::fs::write(&path, b"abc").unwrap();
        let c_path = std::ffi::CString::new(path.to_str().unwrap()).unwrap();
        let mut out = [0u8; 32];
        let rc = unsafe { rt_sha256_file_raw_v1(c_path.as_ptr(), out.as_mut_ptr()) };
        std::fs::remove_file(&path).ok();
        assert_eq!(rc, 1);
        assert_eq!(
            digest_hex(&out),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn test_rt_sha256_file_raw_v1_empty_file() {
        let dir = std::env::temp_dir();
        let path = dir.join(format!("rt_sha256_file_raw_v1_empty_{}.txt", std::process::id()));
        std::fs::write(&path, b"").unwrap();
        let c_path = std::ffi::CString::new(path.to_str().unwrap()).unwrap();
        let mut out = [0u8; 32];
        let rc = unsafe { rt_sha256_file_raw_v1(c_path.as_ptr(), out.as_mut_ptr()) };
        std::fs::remove_file(&path).ok();
        assert_eq!(rc, 1);
        assert_eq!(
            digest_hex(&out),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn test_rt_sha256_file_raw_v1_fails_closed() {
        let mut out = [0u8; 32];
        // Null path.
        assert_eq!(
            unsafe { rt_sha256_file_raw_v1(std::ptr::null(), out.as_mut_ptr()) },
            0
        );
        // Empty path.
        let empty = std::ffi::CString::new("").unwrap();
        assert_eq!(unsafe { rt_sha256_file_raw_v1(empty.as_ptr(), out.as_mut_ptr()) }, 0);
        // Null out.
        let some_path = std::ffi::CString::new("/does/not/exist").unwrap();
        assert_eq!(
            unsafe { rt_sha256_file_raw_v1(some_path.as_ptr(), std::ptr::null_mut()) },
            0
        );
        // Nonexistent file.
        assert_eq!(
            unsafe { rt_sha256_file_raw_v1(some_path.as_ptr(), out.as_mut_ptr()) },
            0
        );
    }
}
