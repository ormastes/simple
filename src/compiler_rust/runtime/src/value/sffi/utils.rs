//! Utility SFFI functions for Simple runtime.
//!
//! - Base64 encoding/decoding: core algorithm in src/runtime/runtime_base64.c
//! - FNV-1a hash: implementation in src/runtime/runtime_hash.c

use crate::value::RuntimeValue;
use crate::value::collections::rt_string_new;

mod c_sffi {
    extern "C" {
        #[link_name = "__c_rt_base64_encode"]
        pub(super) fn base64_encode(input: *const u8, input_len: u64, output: *mut u8, output_cap: u64) -> i64;
        #[link_name = "__c_rt_base64_decode"]
        pub(super) fn base64_decode(input: *const u8, input_len: u64, output: *mut u8, output_cap: u64) -> i64;
        pub(super) fn rt_fnv_hash(data_ptr: *const u8, data_len: u64) -> u64;
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_base64_decode(input_ptr: *const u8, input_len: u64) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }
    let out_cap = ((input_len / 4) + 1) * 3;
    let mut buf = vec![0u8; out_cap as usize];
    let written = c_sffi::base64_decode(input_ptr, input_len, buf.as_mut_ptr(), out_cap);
    if written < 0 {
        return RuntimeValue::NIL;
    }
    rt_string_new(buf.as_ptr(), written as u64)
}

#[no_mangle]
pub unsafe extern "C" fn rt_base64_encode(input_ptr: *const u8, input_len: u64) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }
    let out_cap = ((input_len + 2) / 3) * 4;
    let mut buf = vec![0u8; out_cap as usize];
    let written = c_sffi::base64_encode(input_ptr, input_len, buf.as_mut_ptr(), out_cap);
    if written < 0 {
        return RuntimeValue::NIL;
    }
    rt_string_new(buf.as_ptr(), written as u64)
}

#[inline(always)]
pub unsafe fn rt_fnv_hash(data_ptr: *const u8, data_len: u64) -> u64 {
    c_sffi::rt_fnv_hash(data_ptr, data_len)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};

    unsafe fn extract_string(val: RuntimeValue) -> String {
        if val.is_nil() {
            return String::new();
        }
        let len = rt_string_len(val);
        let ptr = rt_string_data(val);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn test_base64_encode_basic() {
        unsafe {
            let (ptr, len) = str_to_ptr("Hello");
            let encoded = rt_base64_encode(ptr, len);
            assert!(!encoded.is_nil());
            assert_eq!(extract_string(encoded), "SGVsbG8=");
        }
    }

    #[test]
    fn test_base64_encode_various() {
        unsafe {
            let cases = [
                ("", ""),
                ("f", "Zg=="),
                ("fo", "Zm8="),
                ("foo", "Zm9v"),
                ("foob", "Zm9vYg=="),
                ("fooba", "Zm9vYmE="),
                ("foobar", "Zm9vYmFy"),
            ];
            for (input, expected) in cases {
                let (ptr, len) = str_to_ptr(input);
                let encoded = rt_base64_encode(ptr, len);
                assert_eq!(extract_string(encoded), expected, "Failed for '{}'", input);
            }
        }
    }

    #[test]
    fn test_base64_decode_basic() {
        unsafe {
            let (ptr, len) = str_to_ptr("SGVsbG8=");
            let decoded = rt_base64_decode(ptr, len);
            assert!(!decoded.is_nil());
            assert_eq!(extract_string(decoded), "Hello");
        }
    }

    #[test]
    fn test_base64_decode_various() {
        unsafe {
            let cases = [
                ("", ""),
                ("Zg==", "f"),
                ("Zm8=", "fo"),
                ("Zm9v", "foo"),
                ("Zm9vYg==", "foob"),
                ("Zm9vYmE=", "fooba"),
                ("Zm9vYmFy", "foobar"),
            ];
            for (input, expected) in cases {
                let (ptr, len) = str_to_ptr(input);
                let decoded = rt_base64_decode(ptr, len);
                assert_eq!(extract_string(decoded), expected, "Failed for '{}'", input);
            }
        }
    }

    #[test]
    fn test_base64_round_trip() {
        unsafe {
            for input in ["Hello, World!", "Simple Language", "1234567890"] {
                let (ptr, len) = str_to_ptr(input);
                let encoded = rt_base64_encode(ptr, len);
                let enc_str = extract_string(encoded);
                let (ep, el) = str_to_ptr(&enc_str);
                let decoded = rt_base64_decode(ep, el);
                assert_eq!(extract_string(decoded), input);
            }
        }
    }

    #[test]
    fn test_base64_null() {
        unsafe {
            assert!(rt_base64_encode(std::ptr::null(), 10).is_nil());
            assert!(rt_base64_decode(std::ptr::null(), 10).is_nil());
        }
    }

    #[test]
    fn test_base64_decode_whitespace() {
        unsafe {
            let (ptr, len) = str_to_ptr("SGVs bG8=");
            assert_eq!(extract_string(rt_base64_decode(ptr, len)), "Hello");
            let (ptr, len) = str_to_ptr("SGVs\nbG8=");
            assert_eq!(extract_string(rt_base64_decode(ptr, len)), "Hello");
        }
    }

    #[test]
    fn test_fnv_hash_basic() {
        unsafe {
            let (ptr, len) = str_to_ptr("Hello");
            let hash = rt_fnv_hash(ptr, len);
            assert_ne!(hash, 0);
            assert_eq!(hash, rt_fnv_hash(ptr, len));
        }
    }

    #[test]
    fn test_fnv_hash_empty() {
        unsafe {
            let (ptr, len) = str_to_ptr("");
            assert_eq!(rt_fnv_hash(ptr, len), 0xcbf29ce484222325);
        }
    }

    #[test]
    fn test_fnv_hash_null() {
        unsafe {
            assert_eq!(rt_fnv_hash(std::ptr::null(), 10), 0);
        }
    }
}
