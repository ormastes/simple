//! Interpreter-side handlers for native PBKDF2-HMAC helpers.
//!
//! These mirror `signatures.rs`'s `Value::Array(Arc<Vec<Value::Int>>)`
//! `[u8]` shape so `bin/simple test` can short-circuit the pure-Simple
//! PBKDF2 inner loop in `src/lib/common/crypto/pbkdf2.spl` for
//! high-iteration test vectors that otherwise blow past the 60 s
//! test-runner watchdog.
//!
//! See `simple-runtime`'s `value::pbkdf2_native` for the underlying
//! implementation (RustCrypto `pbkdf2 = 0.11` + `hmac` + `sha1` + `sha2`),
//! and `doc/02_requirements/feature/pbkdf2_native_runtime_helpers_2026-05-01.md`
//! for the FR.
//!
//! # Symbols
//! - `rt_pbkdf2_hmac_sha1(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
//! - `rt_pbkdf2_hmac_sha256(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
//! - `rt_pbkdf2_hmac_sha384(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
//! - `rt_pbkdf2_hmac_sha512(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`

use crate::error::CompileError;
use crate::value::Value;
use std::sync::Arc;

use simple_runtime::value::pbkdf2_native;

/// Extract a `Vec<u8>` from a `Value::Array` of `Value::Int` entries.
/// Mirrors `signatures.rs::extract_bytes` — `i as u8` truncates to the
/// low 8 bits so signed-wraparound byte values round-trip correctly.
fn extract_bytes(args: &[Value], index: usize) -> Vec<u8> {
    match args.get(index) {
        Some(Value::Array(arr)) => arr
            .iter()
            .filter_map(|v| match v {
                Value::Int(i) => Some(*i as u8),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn extract_i64(args: &[Value], index: usize) -> i64 {
    match args.get(index) {
        Some(Value::Int(i)) => *i,
        _ => 0,
    }
}

fn bytes_to_value(bytes: &[u8]) -> Value {
    Value::Array(Arc::new(bytes.iter().map(|b| Value::Int(*b as i64)).collect()))
}

/// `rt_pbkdf2_hmac_sha1(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
pub fn rt_pbkdf2_hmac_sha1(args: &[Value]) -> Result<Value, CompileError> {
    let password = extract_bytes(args, 0);
    let salt = extract_bytes(args, 1);
    let iterations = extract_i64(args, 2);
    let dk_len = extract_i64(args, 3);
    let out = pbkdf2_native::pbkdf2_hmac_sha1(&password, &salt, iterations, dk_len);
    Ok(bytes_to_value(&out))
}

/// `rt_pbkdf2_hmac_sha256(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
pub fn rt_pbkdf2_hmac_sha256(args: &[Value]) -> Result<Value, CompileError> {
    let password = extract_bytes(args, 0);
    let salt = extract_bytes(args, 1);
    let iterations = extract_i64(args, 2);
    let dk_len = extract_i64(args, 3);
    let out = pbkdf2_native::pbkdf2_hmac_sha256(&password, &salt, iterations, dk_len);
    Ok(bytes_to_value(&out))
}

/// `rt_pbkdf2_hmac_sha384(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
pub fn rt_pbkdf2_hmac_sha384(args: &[Value]) -> Result<Value, CompileError> {
    let password = extract_bytes(args, 0);
    let salt = extract_bytes(args, 1);
    let iterations = extract_i64(args, 2);
    let dk_len = extract_i64(args, 3);
    let out = pbkdf2_native::pbkdf2_hmac_sha384(&password, &salt, iterations, dk_len);
    Ok(bytes_to_value(&out))
}

/// `rt_pbkdf2_hmac_sha512(password: [u8], salt: [u8], iterations: i64, dk_len: i64) -> [u8]`
pub fn rt_pbkdf2_hmac_sha512(args: &[Value]) -> Result<Value, CompileError> {
    let password = extract_bytes(args, 0);
    let salt = extract_bytes(args, 1);
    let iterations = extract_i64(args, 2);
    let dk_len = extract_i64(args, 3);
    let out = pbkdf2_native::pbkdf2_hmac_sha512(&password, &salt, iterations, dk_len);
    Ok(bytes_to_value(&out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arr_of_bytes(bytes: &[u8]) -> Value {
        Value::Array(Arc::new(bytes.iter().map(|b| Value::Int(*b as i64)).collect()))
    }

    fn value_to_hex(v: &Value) -> String {
        match v {
            Value::Array(arr) => {
                let mut s = String::with_capacity(arr.len() * 2);
                for entry in arr.iter() {
                    if let Value::Int(i) = entry {
                        s.push_str(&format!("{:02x}", *i as u8));
                    }
                }
                s
            }
            _ => String::new(),
        }
    }

    #[test]
    fn dispatch_sha256_c4096() {
        let args = vec![
            arr_of_bytes(b"password"),
            arr_of_bytes(b"salt"),
            Value::Int(4096),
            Value::Int(32),
        ];
        let result = rt_pbkdf2_hmac_sha256(&args).unwrap();
        assert_eq!(
            value_to_hex(&result),
            "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"
        );
    }

    #[test]
    fn dispatch_sha512_c1() {
        let args = vec![
            arr_of_bytes(b"password"),
            arr_of_bytes(b"salt"),
            Value::Int(1),
            Value::Int(64),
        ];
        let result = rt_pbkdf2_hmac_sha512(&args).unwrap();
        assert_eq!(
            value_to_hex(&result),
            "867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252\
             c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce"
        );
    }

    #[test]
    fn dispatch_sha384_c1() {
        let args = vec![
            arr_of_bytes(b"password"),
            arr_of_bytes(b"salt"),
            Value::Int(1),
            Value::Int(48),
        ];
        let result = rt_pbkdf2_hmac_sha384(&args).unwrap();
        assert_eq!(
            value_to_hex(&result),
            "c0e14f06e49e32d73f9f52ddf1d0c5c7191609233631dadd76a567db42b78676\
             b38fc800cc53ddb642f5c74442e62be4"
        );
    }
}
