//! Utility FFI functions for Simple runtime.
//!
//! This module provides miscellaneous utility functions:
//! - Base64 encoding and decoding
//! - FNV-1a hash function (non-cryptographic)

use crate::value::RuntimeValue;
use crate::value::collections::rt_string_new;

// ============================================================================
// Base64 Encoding/Decoding
// ============================================================================

/// Decode base64 string to bytes
/// Returns a RuntimeValue string containing the decoded bytes, or NIL on error
#[no_mangle]
pub unsafe extern "C" fn rt_base64_decode(input_ptr: *const u8, input_len: u64) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let input_bytes = std::slice::from_raw_parts(input_ptr, input_len as usize);
    let input_str = match std::str::from_utf8(input_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    // Base64 decoding lookup table
    const DECODE_TABLE: [u8; 128] = [
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62,
        255, 255, 255, 63, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 0, 255, 255, 255, 0, 1, 2, 3, 4, 5,
        6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255, 255, 26,
        27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 255, 255,
        255, 255, 255,
    ];

    let mut result = Vec::new();
    let input_chars: Vec<u8> = input_str.bytes().filter(|&b| !b.is_ascii_whitespace()).collect();

    let mut i = 0;
    while i < input_chars.len() {
        // Get 4 characters (or remaining)
        let mut chunk = [0u8; 4];
        let mut chunk_len = 0;

        while chunk_len < 4 && i < input_chars.len() {
            let c = input_chars[i];
            i += 1;

            if c == b'=' {
                chunk[chunk_len] = 0;
                chunk_len += 1;
            } else if (c as usize) < 128 && DECODE_TABLE[c as usize] != 255 {
                chunk[chunk_len] = DECODE_TABLE[c as usize];
                chunk_len += 1;
            }
        }

        if chunk_len >= 2 {
            result.push((chunk[0] << 2) | (chunk[1] >> 4));
        }
        if chunk_len >= 3 {
            result.push((chunk[1] << 4) | (chunk[2] >> 2));
        }
        if chunk_len >= 4 {
            result.push((chunk[2] << 6) | chunk[3]);
        }
    }

    // Remove padding bytes
    while result.last() == Some(&0) && input_str.ends_with('=') {
        result.pop();
    }

    // Convert to string (assuming UTF-8)
    match String::from_utf8(result) {
        Ok(decoded) => {
            let bytes = decoded.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Encode bytes to base64 string
/// Returns a RuntimeValue string containing the base64-encoded data, or NIL on error
#[no_mangle]
pub unsafe extern "C" fn rt_base64_encode(input_ptr: *const u8, input_len: u64) -> RuntimeValue {
    if input_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let input_bytes = std::slice::from_raw_parts(input_ptr, input_len as usize);

    const ENCODE_TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    let mut result = Vec::new();
    let mut i = 0;

    while i < input_bytes.len() {
        let b1 = input_bytes[i];
        let b2 = if i + 1 < input_bytes.len() {
            input_bytes[i + 1]
        } else {
            0
        };
        let b3 = if i + 2 < input_bytes.len() {
            input_bytes[i + 2]
        } else {
            0
        };

        result.push(ENCODE_TABLE[(b1 >> 2) as usize]);
        result.push(ENCODE_TABLE[(((b1 & 0x03) << 4) | (b2 >> 4)) as usize]);

        if i + 1 < input_bytes.len() {
            result.push(ENCODE_TABLE[(((b2 & 0x0F) << 2) | (b3 >> 6)) as usize]);
        } else {
            result.push(b'=');
        }

        if i + 2 < input_bytes.len() {
            result.push(ENCODE_TABLE[(b3 & 0x3F) as usize]);
        } else {
            result.push(b'=');
        }

        i += 3;
    }

    match String::from_utf8(result) {
        Ok(encoded) => {
            let bytes = encoded.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

// ============================================================================
// Hash Functions
// ============================================================================

/// FNV-1a hash function (Fowler-Noll-Vo hash)
/// Fast non-cryptographic hash function suitable for hash tables
/// Returns 64-bit hash value, or 0 if input is null
#[no_mangle]
pub unsafe extern "C" fn rt_fnv_hash(data_ptr: *const u8, data_len: u64) -> u64 {
    if data_ptr.is_null() {
        return 0;
    }

    let data = std::slice::from_raw_parts(data_ptr, data_len as usize);
    let mut hash: u64 = 0xcbf29ce484222325; // FNV offset basis
    const FNV_PRIME: u64 = 0x100000001b3; // FNV prime

    for &byte in data {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }

    hash
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};

    // Helper to convert RuntimeValue string to Rust String
    unsafe fn extract_string(val: RuntimeValue) -> String {
        if val.is_nil() {
            return String::new();
        }
        let len = rt_string_len(val);
        let ptr = rt_string_data(val);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

    // Helper to create C-style string pointer
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    #[test]
    fn test_base64_encode_basic() {
        unsafe {
            // "Hello" -> "SGVsbG8="
            let (ptr, len) = str_to_ptr("Hello");
            let encoded = rt_base64_encode(ptr, len);
            assert!(!encoded.is_nil());

            let encoded_str = extract_string(encoded);
            assert_eq!(encoded_str, "SGVsbG8=");
        }
    }

    #[test]
    fn test_base64_encode_various() {
        unsafe {
            // Test various strings
            let test_cases = vec![
                ("", ""),
                ("f", "Zg=="),
                ("fo", "Zm8="),
                ("foo", "Zm9v"),
                ("foob", "Zm9vYg=="),
                ("fooba", "Zm9vYmE="),
                ("foobar", "Zm9vYmFy"),
            ];

            for (input, expected) in test_cases {
                let (ptr, len) = str_to_ptr(input);
                let encoded = rt_base64_encode(ptr, len);
                let encoded_str = extract_string(encoded);
                assert_eq!(encoded_str, expected, "Failed for input: '{}'", input);
            }
        }
    }

    #[test]
    fn test_base64_decode_basic() {
        unsafe {
            // "SGVsbG8=" -> "Hello"
            let (ptr, len) = str_to_ptr("SGVsbG8=");
            let decoded = rt_base64_decode(ptr, len);
            assert!(!decoded.is_nil());

            let decoded_str = extract_string(decoded);
            assert_eq!(decoded_str, "Hello");
        }
    }

    #[test]
    fn test_base64_decode_various() {
        unsafe {
            let test_cases = vec![
                ("", ""),
                ("Zg==", "f"),
                ("Zm8=", "fo"),
                ("Zm9v", "foo"),
                ("Zm9vYg==", "foob"),
                ("Zm9vYmE=", "fooba"),
                ("Zm9vYmFy", "foobar"),
            ];

            for (input, expected) in test_cases {
                let (ptr, len) = str_to_ptr(input);
                let decoded = rt_base64_decode(ptr, len);
                let decoded_str = extract_string(decoded);
                assert_eq!(decoded_str, expected, "Failed for input: '{}'", input);
            }
        }
    }

    #[test]
    fn test_base64_round_trip() {
        unsafe {
            let test_strings = vec![
                "Hello, World!",
                "Simple Language",
                "Base64 encoding test",
                "1234567890",
                "Special chars: !@#$%^&*()",
            ];

            for input in test_strings {
                let (ptr, len) = str_to_ptr(input);
                let encoded = rt_base64_encode(ptr, len);
                assert!(!encoded.is_nil());

                let encoded_str = extract_string(encoded);
                let (enc_ptr, enc_len) = str_to_ptr(&encoded_str);
                let decoded = rt_base64_decode(enc_ptr, enc_len);
                assert!(!decoded.is_nil());

                let decoded_str = extract_string(decoded);
                assert_eq!(decoded_str, input, "Round trip failed for: '{}'", input);
            }
        }
    }

    #[test]
    fn test_base64_encode_null() {
        unsafe {
            let result = rt_base64_encode(std::ptr::null(), 10);
            assert!(result.is_nil());
        }
    }

    #[test]
    fn test_base64_decode_null() {
        unsafe {
            let result = rt_base64_decode(std::ptr::null(), 10);
            assert!(result.is_nil());
        }
    }

    #[test]
    fn test_base64_decode_whitespace() {
        unsafe {
            // Base64 should ignore whitespace
            let (ptr, len) = str_to_ptr("SGVs bG8=");
            let decoded = rt_base64_decode(ptr, len);
            let decoded_str = extract_string(decoded);
            assert_eq!(decoded_str, "Hello");

            // With newlines
            let (ptr, len) = str_to_ptr("SGVs\nbG8=");
            let decoded = rt_base64_decode(ptr, len);
            let decoded_str = extract_string(decoded);
            assert_eq!(decoded_str, "Hello");
        }
    }

    #[test]
    fn test_fnv_hash_basic() {
        unsafe {
            let (ptr, len) = str_to_ptr("Hello");
            let hash = rt_fnv_hash(ptr, len);
            assert_ne!(hash, 0);

            // Same input should produce same hash
            let hash2 = rt_fnv_hash(ptr, len);
            assert_eq!(hash, hash2);
        }
    }

    #[test]
    fn test_fnv_hash_different_inputs() {
        unsafe {
            let (ptr1, len1) = str_to_ptr("Hello");
            let (ptr2, len2) = str_to_ptr("World");

            let hash1 = rt_fnv_hash(ptr1, len1);
            let hash2 = rt_fnv_hash(ptr2, len2);

            // Different inputs should (very likely) produce different hashes
            assert_ne!(hash1, hash2);
        }
    }

    #[test]
    fn test_fnv_hash_empty() {
        unsafe {
            let (ptr, len) = str_to_ptr("");
            let hash = rt_fnv_hash(ptr, len);

            // Empty string should produce FNV offset basis
            assert_eq!(hash, 0xcbf29ce484222325);
        }
    }

    #[test]
    fn test_fnv_hash_null() {
        unsafe {
            let hash = rt_fnv_hash(std::ptr::null(), 10);
            assert_eq!(hash, 0);
        }
    }

    #[test]
    fn test_fnv_hash_consistency() {
        unsafe {
            // Test that same input always produces same hash (consistency)
            let test_inputs = vec!["", "a", "b", "c", "foo", "bar", "Hello, World!"];

            for input in test_inputs {
                let (ptr, len) = str_to_ptr(input);
                let hash1 = rt_fnv_hash(ptr, len);
                let hash2 = rt_fnv_hash(ptr, len);
                let hash3 = rt_fnv_hash(ptr, len);

                assert_eq!(hash1, hash2, "FNV hash inconsistent for input: '{}'", input);
                assert_eq!(hash2, hash3, "FNV hash inconsistent for input: '{}'", input);
            }

            // Empty string should produce FNV offset basis
            let (ptr, len) = str_to_ptr("");
            let hash = rt_fnv_hash(ptr, len);
            assert_eq!(hash, 0xcbf29ce484222325, "Empty string hash should be FNV offset basis");
        }
    }

    #[test]
    fn test_fnv_hash_avalanche() {
        unsafe {
            // Small changes should produce very different hashes (avalanche effect)
            let (ptr1, len1) = str_to_ptr("test");
            let (ptr2, len2) = str_to_ptr("teSt");

            let hash1 = rt_fnv_hash(ptr1, len1);
            let hash2 = rt_fnv_hash(ptr2, len2);

            assert_ne!(hash1, hash2);

            // Count differing bits (should be roughly 50% for good hash)
            let xor = hash1 ^ hash2;
            let differing_bits = xor.count_ones();
            assert!(differing_bits >= 10, "Too few differing bits: {}", differing_bits);
        }
    }
}
