/// SHA-1 and Base64 functions for the interpreter.
///
/// Provides rt_sha1_* hasher functions and rt_base64_encode for
/// WebSocket handshake support in the web UI server.
use crate::value::Value;
use crate::error::CompileError;
use base64::Engine;
use sha1::{Digest, Sha1};
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref SHA1_STATE: Mutex<HashMap<i64, Vec<u8>>> = Mutex::new(HashMap::new());
    static ref SHA1_COUNTER: Mutex<i64> = Mutex::new(1);
}

#[inline]
fn int_arg(args: &[Value], index: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be an integer"
        ))),
    }
}

fn bytes_arg(args: &[Value], index: usize, symbol: &str) -> Result<Vec<u8>, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_bytes().to_vec()),
        Some(value) => value
            .try_array_bytes()
            .ok_or_else(|| CompileError::runtime(format!("{symbol}: argument {index} must be text or bytes"))),
        None => Err(CompileError::runtime(format!("{symbol}: missing argument {index}"))),
    }
}

fn text_arg<'a>(args: &'a [Value], index: usize, symbol: &str) -> Result<&'a str, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_str()),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be text"
        ))),
    }
}

pub fn rt_sha1_new(_args: &[Value]) -> Result<Value, CompileError> {
    let mut counter = SHA1_COUNTER.lock().unwrap();
    let handle = *counter;
    *counter += 1;
    SHA1_STATE.lock().unwrap().insert(handle, Vec::new());
    Ok(Value::Int(handle))
}

pub fn rt_sha1_write(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_write")?;
    let data = bytes_arg(args, 1, "rt_sha1_write")?;
    let mut state = SHA1_STATE
        .lock()
        .map_err(|_| CompileError::runtime("rt_sha1_write: state lock poisoned".to_string()))?;
    let buf = state
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("rt_sha1_write: invalid SHA-1 handle {handle}")))?;
    buf.extend_from_slice(&data);
    Ok(Value::Nil)
}

pub fn rt_sha1_finish(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_finish")?;
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        let hex = format!("{:x}", result);
        Ok(Value::text(hex))
    } else {
        Err(CompileError::runtime(format!(
            "rt_sha1_finish: invalid SHA-1 handle {handle}"
        )))
    }
}

pub fn rt_sha1_finish_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_finish_bytes")?;
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        Ok(Value::byte_array(result.to_vec()))
    } else {
        Err(CompileError::runtime(format!(
            "rt_sha1_finish_bytes: invalid SHA-1 handle {handle}"
        )))
    }
}

pub fn rt_sha1_reset(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_reset")?;
    let mut state = SHA1_STATE
        .lock()
        .map_err(|_| CompileError::runtime("rt_sha1_reset: state lock poisoned".to_string()))?;
    let buf = state
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("rt_sha1_reset: invalid SHA-1 handle {handle}")))?;
    buf.clear();
    Ok(Value::Nil)
}

pub fn rt_sha1_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_free")?;
    if SHA1_STATE.lock().unwrap().remove(&handle).is_none() {
        return Err(CompileError::runtime(format!(
            "rt_sha1_free: invalid SHA-1 handle {handle}"
        )));
    }
    Ok(Value::Nil)
}

pub fn rt_sha1_finish_base64(args: &[Value]) -> Result<Value, CompileError> {
    let handle = int_arg(args, 0, "rt_sha1_finish_base64")?;
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        let bytes: Vec<u8> = result.to_vec();
        let encoded = base64::engine::general_purpose::STANDARD.encode(&bytes);
        Ok(Value::text(encoded))
    } else {
        Err(CompileError::runtime(format!(
            "rt_sha1_finish_base64: invalid SHA-1 handle {handle}"
        )))
    }
}

pub fn rt_base64_encode(args: &[Value]) -> Result<Value, CompileError> {
    let data = bytes_arg(args, 0, "rt_base64_encode")?;
    let encoded = base64::engine::general_purpose::STANDARD.encode(&data);
    Ok(Value::text(encoded))
}

pub fn rt_base64_decode(args: &[Value]) -> Result<Value, CompileError> {
    let input = text_arg(args, 0, "rt_base64_decode")?;
    match base64::engine::general_purpose::STANDARD.decode(input) {
        Ok(bytes) => Ok(Value::text(String::from_utf8_lossy(&bytes).into_owned())),
        Err(_) => Ok(Value::Nil),
    }
}

/// Constant-time text comparison for the interpreter.
///
/// Mirrors the byte-level semantics of the compiled runtime
/// (`crypto_compare.rs::rt_constant_time_compare`):
///   * length mismatch -> 0 (not equal)
///   * both empty       -> 1 (equal)
///   * otherwise        -> XOR-accumulate over bytes; 1 if accumulator is 0
///
/// The interpreter dispatch is not perf- or side-channel-critical (B6
/// commentary in `constant_time.spl` targets the Cranelift compiled
/// path); this implementation simply matches behaviour.
///
/// Without this case, the unknown-extern fallthrough sends each `Value::Str`
/// argument through `dynamic_sffi::value_to_i64`, which leaks a C-string
/// pointer. The runtime then reinterprets those bits as packed
/// `RuntimeValue`s, `rt_string_data` returns null, and the function
/// returns 0 unconditionally — making `constant_time_compare(a, a)`
/// return false for every input.
pub fn rt_constant_time_compare(args: &[Value]) -> Result<Value, CompileError> {
    let a = match args.first() {
        Some(Value::Str(s)) => s.as_bytes(),
        _ => {
            return Err(CompileError::runtime(
                "rt_constant_time_compare: argument 0 must be text".to_string(),
            ))
        }
    };
    let b = match args.get(1) {
        Some(Value::Str(s)) => s.as_bytes(),
        _ => {
            return Err(CompileError::runtime(
                "rt_constant_time_compare: argument 1 must be text".to_string(),
            ))
        }
    };
    if a.len() != b.len() {
        return Ok(Value::Int(0));
    }
    if a.is_empty() {
        return Ok(Value::Int(1));
    }
    let mut acc: u8 = 0;
    for i in 0..a.len() {
        acc |= a[i] ^ b[i];
    }
    Ok(Value::Int(if acc == 0 { 1 } else { 0 }))
}

/// One-shot SHA-1 hash of text data, returned as lowercase hex string.
///
/// Callable from Simple as: `rt_sha1(data: text) -> text`
pub fn rt_sha1(args: &[Value]) -> Result<Value, CompileError> {
    let data = bytes_arg(args, 0, "rt_sha1")?;
    let mut hasher = Sha1::new();
    hasher.update(&data);
    let result = hasher.finalize();
    Ok(Value::text(format!("{:x}", result)))
}

/// Base64url decode (RFC 4648 section 5, no padding).
///
/// Callable from Simple as: `rt_base64url_decode(encoded: text) -> text`
pub fn rt_base64url_decode(args: &[Value]) -> Result<Value, CompileError> {
    let input = text_arg(args, 0, "rt_base64url_decode")?;
    match base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(input) {
        Ok(bytes) => Ok(Value::text(String::from_utf8_lossy(&bytes).into_owned())),
        Err(_) => Ok(Value::text(String::new())),
    }
}

/// Base64url encode (RFC 4648 section 5, no padding).
///
/// Callable from Simple as: `rt_base64url_encode(input: text, len: i64) -> text`
pub fn rt_base64url_encode(args: &[Value]) -> Result<Value, CompileError> {
    let data = bytes_arg(args, 0, "rt_base64url_encode")?;
    // Second argument (len) can limit how many bytes to encode
    let requested = int_arg(args, 1, "rt_base64url_encode")?;
    let limit = if requested > 0 && (requested as usize) < data.len() {
        requested as usize
    } else {
        data.len()
    };
    let encoded = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&data[..limit]);
    Ok(Value::text(encoded))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crypto_bridge_rejects_fabricated_inputs_and_invalid_handles() {
        assert!(rt_sha1_write(&[]).is_err());
        assert!(rt_sha1_write(&[Value::Int(1), Value::Int(0), Value::Int(4)]).is_err());
        assert!(rt_sha1_finish(&[Value::Int(i64::MAX)]).is_err());
        assert!(rt_sha1_reset(&[Value::Bool(false)]).is_err());
        assert!(rt_sha1_free(&[Value::Int(i64::MAX)]).is_err());
        assert!(rt_base64_encode(&[]).is_err());
        assert!(rt_base64_decode(&[Value::Int(0)]).is_err());
        assert!(rt_constant_time_compare(&[Value::text("a"), Value::Nil]).is_err());
        assert!(rt_sha1(&[]).is_err());
        assert!(rt_base64url_encode(&[Value::text("value"), Value::Nil]).is_err());
    }

    #[test]
    fn explicit_empty_crypto_inputs_remain_valid() {
        assert_eq!(
            rt_base64_encode(&[Value::byte_array(Vec::new())]).unwrap(),
            Value::text("")
        );
        assert_eq!(
            rt_constant_time_compare(&[Value::text(""), Value::text("")]).unwrap(),
            Value::Int(1)
        );
    }
}
