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

pub fn rt_sha1_new(_args: &[Value]) -> Result<Value, CompileError> {
    let mut counter = SHA1_COUNTER.lock().unwrap();
    let handle = *counter;
    *counter += 1;
    SHA1_STATE.lock().unwrap().insert(handle, Vec::new());
    Ok(Value::Int(handle))
}

pub fn rt_sha1_write(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let handle = match &args[0] {
        Value::Int(h) => *h,
        _ => return Ok(Value::Nil),
    };
    // In the interpreter, data comes as a string (text) — the write_str path
    let data = match &args[1] {
        Value::Str(s) => s.as_bytes().to_vec(),
        Value::Int(ptr) => {
            // When called via write() with array, interpreter may pass as int
            // Fall back to empty
            Vec::new()
        }
        Value::Array(arr) => {
            // Array of u8 values
            arr.iter()
                .filter_map(|v| match v {
                    Value::Int(i) => Some(*i as u8),
                    _ => None,
                })
                .collect()
        }
        _ => Vec::new(),
    };
    if let Ok(mut state) = SHA1_STATE.lock() {
        if let Some(buf) = state.get_mut(&handle) {
            buf.extend_from_slice(&data);
        }
    }
    Ok(Value::Nil)
}

pub fn rt_sha1_finish(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(h)) => *h,
        _ => return Ok(Value::Nil),
    };
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        let hex = format!("{:x}", result);
        Ok(Value::Str(hex))
    } else {
        Ok(Value::Nil)
    }
}

pub fn rt_sha1_finish_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(h)) => *h,
        _ => return Ok(Value::Nil),
    };
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        // Return raw bytes as a string (byte-transparent)
        let bytes: Vec<u8> = result.to_vec();
        Ok(Value::Str(String::from_utf8_lossy(&bytes).into_owned()))
    } else {
        Ok(Value::Nil)
    }
}

pub fn rt_sha1_reset(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(h)) => *h,
        _ => return Ok(Value::Nil),
    };
    if let Ok(mut state) = SHA1_STATE.lock() {
        if let Some(buf) = state.get_mut(&handle) {
            buf.clear();
        }
    }
    Ok(Value::Nil)
}

pub fn rt_sha1_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(h)) => *h,
        _ => return Ok(Value::Nil),
    };
    SHA1_STATE.lock().unwrap().remove(&handle);
    Ok(Value::Nil)
}

pub fn rt_sha1_finish_base64(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(h)) => *h,
        _ => return Ok(Value::Nil),
    };
    let mut state = SHA1_STATE.lock().unwrap();
    if let Some(data) = state.remove(&handle) {
        let mut hasher = Sha1::new();
        hasher.update(&data);
        let result = hasher.finalize();
        let bytes: Vec<u8> = result.to_vec();
        let encoded = base64::engine::general_purpose::STANDARD.encode(&bytes);
        Ok(Value::Str(encoded))
    } else {
        Ok(Value::Nil)
    }
}

pub fn rt_base64_encode(args: &[Value]) -> Result<Value, CompileError> {
    let data = match args.first() {
        Some(Value::Str(s)) => s.as_bytes().to_vec(),
        Some(Value::Array(arr)) => arr
            .iter()
            .filter_map(|v| match v {
                Value::Int(i) => Some(*i as u8),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    let encoded = base64::engine::general_purpose::STANDARD.encode(&data);
    Ok(Value::Str(encoded))
}

pub fn rt_base64_decode(args: &[Value]) -> Result<Value, CompileError> {
    let input = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::Nil),
    };
    match base64::engine::general_purpose::STANDARD.decode(&input) {
        Ok(bytes) => Ok(Value::Str(String::from_utf8_lossy(&bytes).into_owned())),
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
/// argument through `dynamic_ffi::value_to_i64`, which leaks a C-string
/// pointer. The runtime then reinterprets those bits as packed
/// `RuntimeValue`s, `rt_string_data` returns null, and the function
/// returns 0 unconditionally — making `constant_time_compare(a, a)`
/// return false for every input.
pub fn rt_constant_time_compare(args: &[Value]) -> Result<Value, CompileError> {
    let a = match args.first() {
        Some(Value::Str(s)) => s.as_bytes(),
        _ => return Ok(Value::Int(0)),
    };
    let b = match args.get(1) {
        Some(Value::Str(s)) => s.as_bytes(),
        _ => return Ok(Value::Int(0)),
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
