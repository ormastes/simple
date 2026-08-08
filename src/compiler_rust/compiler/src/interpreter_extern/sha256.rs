//! Streaming SHA-256 hasher externs for the **interpreter**.
//!
//! The native runtime already exposes `rt_sha256_new` / `rt_sha256_write` /
//! `rt_sha256_finish` (`src/compiler_rust/runtime/src/value/sffi/hash/sha256.rs`),
//! but those were reachable **only from AOT/compiled code**, for two reasons:
//!
//! 1. **No `EXTERN_DISPATCH` entry.** `interpreter_extern/mod.rs` registered the
//!    whole `rt_sha1_*` family and none of `rt_sha256_*`, so an interpreted call
//!    fell through to `dynamic_sffi::try_call_dynamic`.
//! 2. **The dynamic fallthrough cannot express the native signature.**
//!    `dynamic_sffi` coerces every argument *and* the return value through
//!    `i64`. The native `rt_sha256_write` takes a raw `(*const u8, u64)`
//!    pointer pair — an interpreted `[u8]` is a `Vec<Value>`, not a byte
//!    buffer, so `value_to_i64` hands it an unrelated pointer — and
//!    `rt_sha256_finish` returns a **packed `RuntimeValue`**, not an `i64`, so
//!    the returned bits get reinterpreted as an integer. That is why the family
//!    could never have been reached by "linking harder"; it needs
//!    interpreter-native handlers, exactly as `rt_sha1_*` already has in
//!    `crypto.rs`.
//!
//! Because a *wrong* digest is worse than a missing one (this tree has a filed
//! history of fabricated and silently-empty crypto results), byte extraction
//! here is **strict**: any array element that is not an integral byte is a hard
//! error, never a silently dropped element. Contrast
//! `crypto.rs::rt_sha1_write`, which `filter_map`s non-`Int` elements away —
//! that silently hashes a *shorter* buffer when handed a real `[u8]`, whose
//! elements are `Value::UInt { width: 8 }` rather than `Value::Int`.
//!
//! Input is streamed into the digest context rather than accumulated into a
//! second `Vec<u8>` per handle, so a multi-megabyte payload costs one pass.
//!
//! `ring` is used because it is already a dependency of this crate (see
//! `sha512.rs`); no new crate is introduced.
//!
//! **Deliberately NOT registered here:** `rt_sha256_finish_bytes` (the native
//! form packs 32 raw, non-UTF-8 bytes into a runtime string; no interpreter
//! `Value` reproduces that packing without either lossy corruption or a
//! type divergence between lanes) and any one-shot `rt_sha256_hex` (it has no
//! native counterpart, so a `.spl` caller would link on the interpreter and
//! fail to link AOT). Only the five symbols whose observable behaviour is
//! identical in both lanes are registered, so `.spl` code written against them
//! behaves the same interpreted and compiled.

use crate::error::CompileError;
use crate::value::Value;
use ring::digest::{Context, SHA256};
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex};

lazy_static::lazy_static! {
    static ref SHA256_STATE: Mutex<HashMap<i64, Context>> = Mutex::new(HashMap::new());
}

static SHA256_COUNTER: AtomicI64 = AtomicI64::new(1);

fn hex_of(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push_str(&format!("{:02x}", b));
    }
    out
}

/// Extract one byte from an interpreted array element.
///
/// Accepts every integral spelling the interpreter produces for a `[u8]`
/// element: `u8` literals arrive as `Value::UInt { width: 8 }`, while
/// arithmetic results and `as i64` casts arrive as `Value::Int`. Everything
/// else is rejected.
fn element_byte(v: &Value, index: usize) -> Result<u8, CompileError> {
    match v {
        Value::Int(i) => {
            if *i < 0 || *i > 255 {
                Err(CompileError::runtime(format!(
                    "rt_sha256_write: byte {} out of range (got {})",
                    index, i
                )))
            } else {
                Ok(*i as u8)
            }
        }
        Value::UInt { value, .. } => {
            if *value > 255 {
                Err(CompileError::runtime(format!(
                    "rt_sha256_write: byte {} out of range (got {})",
                    index, value
                )))
            } else {
                Ok(*value as u8)
            }
        }
        Value::Bool(b) => Ok(u8::from(*b)),
        _ => Err(CompileError::runtime(format!(
            "rt_sha256_write: element {} is not a byte",
            index
        ))),
    }
}

/// Collect the payload argument into bytes.
///
/// `text` hashes its UTF-8 bytes, `StrBytes` its raw bytes, arrays hash
/// element-wise. Anything else errors rather than hashing an empty buffer.
fn payload_bytes(v: &Value) -> Result<Vec<u8>, CompileError> {
    match v {
        Value::Str(s) => Ok(s.as_bytes().to_vec()),
        Value::StrBytes(b) => Ok(b.as_ref().clone()),
        Value::Array(arr) | Value::FrozenArray(arr) => {
            let mut out = Vec::with_capacity(arr.len());
            for (i, e) in arr.iter().enumerate() {
                out.push(element_byte(e, i)?);
            }
            Ok(out)
        }
        Value::FixedSizeArray { data, .. } => {
            let mut out = Vec::with_capacity(data.len());
            for (i, e) in data.iter().enumerate() {
                out.push(element_byte(e, i)?);
            }
            Ok(out)
        }
        _ => Err(CompileError::runtime(
            "rt_sha256_write: unsupported payload type (expected text or [u8])".to_string(),
        )),
    }
}

fn handle_of(args: &[Value], who: &str) -> Result<i64, CompileError> {
    match args.first() {
        Some(Value::Int(h)) => Ok(*h),
        Some(Value::UInt { value, .. }) => Ok(*value as i64),
        _ => Err(CompileError::runtime(format!("{}: missing hasher handle", who))),
    }
}

/// `rt_sha256_new() -> i64`
pub fn rt_sha256_new(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = SHA256_COUNTER.fetch_add(1, Ordering::SeqCst);
    SHA256_STATE.lock().unwrap().insert(handle, Context::new(&SHA256));
    Ok(Value::Int(handle))
}

/// `rt_sha256_write(hasher: i64, data: [u8] | text, len: i64)`
///
/// The trailing `len` exists for the compiled `(ptr, len)` ABI and is honoured
/// here as a truncation bound: a non-negative `len` shorter than the payload
/// hashes only that prefix. A `len` longer than the payload is an error rather
/// than a silent short hash.
pub fn rt_sha256_write(args: &[Value]) -> Result<Value, CompileError> {
    let handle = handle_of(args, "rt_sha256_write")?;
    let payload = match args.get(1) {
        Some(v) => payload_bytes(v)?,
        None => return Err(CompileError::runtime("rt_sha256_write: missing data".to_string())),
    };
    let limit = match args.get(2) {
        Some(Value::Int(n)) if *n >= 0 => *n as usize,
        Some(Value::UInt { value, .. }) => *value as usize,
        _ => payload.len(),
    };
    if limit > payload.len() {
        return Err(CompileError::runtime(format!(
            "rt_sha256_write: len {} exceeds payload length {}",
            limit,
            payload.len()
        )));
    }
    let mut state = SHA256_STATE.lock().unwrap();
    match state.get_mut(&handle) {
        Some(ctx) => {
            ctx.update(&payload[..limit]);
            Ok(Value::Nil)
        }
        None => Err(CompileError::runtime(format!(
            "rt_sha256_write: unknown hasher handle {}",
            handle
        ))),
    }
}

/// `rt_sha256_finish(hasher: i64) -> text` — 64-char lowercase hex.
///
/// Consumes the handle, matching the native runtime's `map.remove`.
pub fn rt_sha256_finish(args: &[Value]) -> Result<Value, CompileError> {
    let handle = handle_of(args, "rt_sha256_finish")?;
    let ctx = SHA256_STATE.lock().unwrap().remove(&handle);
    match ctx {
        Some(c) => Ok(Value::text(hex_of(c.finish().as_ref()))),
        None => Err(CompileError::runtime(format!(
            "rt_sha256_finish: unknown hasher handle {}",
            handle
        ))),
    }
}

/// `rt_sha256_reset(hasher: i64)`
pub fn rt_sha256_reset(args: &[Value]) -> Result<Value, CompileError> {
    let handle = handle_of(args, "rt_sha256_reset")?;
    let mut state = SHA256_STATE.lock().unwrap();
    match state.get_mut(&handle) {
        Some(ctx) => {
            *ctx = Context::new(&SHA256);
            Ok(Value::Nil)
        }
        None => Err(CompileError::runtime(format!(
            "rt_sha256_reset: unknown hasher handle {}",
            handle
        ))),
    }
}

/// `rt_sha256_free(hasher: i64)` — idempotent.
pub fn rt_sha256_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = handle_of(args, "rt_sha256_free")?;
    SHA256_STATE.lock().unwrap().remove(&handle);
    Ok(Value::Nil)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Known-answer vectors transcribed from the **published standard**, not
    /// produced by this implementation:
    ///
    /// - `"abc"` and the 448-bit two-block message are FIPS 180-4 Appendix B.1
    ///   and B.2, reproduced verbatim as TEST1 / TEST2_1 in **RFC 6234 s8.5**
    ///   and in NIST CSRC's byte-oriented `SHA256.pdf` examples.
    /// - The empty-string digest is the published SHA-256 of the zero-length
    ///   message (NIST CAVP short-message vector `Len = 0`).
    ///
    ///   ""     -> e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
    ///   "abc"  -> ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
    ///   "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
    ///          -> 248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1
    const KAT: &[(&str, &str)] = &[
        ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        (
            "abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
    ];

    fn text_of(v: Value) -> String {
        match v {
            Value::Str(s) => String::from_utf8_lossy(s.as_bytes()).into_owned(),
            other => panic!("expected text, got {:?}", other),
        }
    }

    fn new_handle() -> i64 {
        match rt_sha256_new(&[]).unwrap() {
            Value::Int(h) => h,
            other => panic!("handle: {:?}", other),
        }
    }

    fn digest_text(input: &str) -> String {
        let handle = new_handle();
        rt_sha256_write(&[
            Value::Int(handle),
            Value::text(input.to_string()),
            Value::Int(input.len() as i64),
        ])
        .unwrap();
        text_of(rt_sha256_finish(&[Value::Int(handle)]).unwrap())
    }

    #[test]
    fn streaming_matches_published_vectors() {
        for (input, expected) in KAT {
            assert_eq!(&digest_text(input), expected, "vector {:?}", input);
        }
    }

    /// A `[u8]` array whose elements are `UInt { width: 8 }` -- the shape the
    /// interpreter actually produces -- must hash identically to the text.
    #[test]
    fn u8_array_matches_text_and_is_not_silently_dropped() {
        let handle = new_handle();
        let arr = Value::Array(Arc::new(
            b"abc"
                .iter()
                .map(|b| Value::UInt {
                    value: *b as u64,
                    width: 8,
                })
                .collect(),
        ));
        rt_sha256_write(&[Value::Int(handle), arr, Value::Int(3)]).unwrap();
        assert_eq!(
            text_of(rt_sha256_finish(&[Value::Int(handle)]).unwrap()),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    /// Multi-chunk streaming must equal the single-write digest.
    #[test]
    fn chunked_writes_equal_single_write() {
        let handle = new_handle();
        for chunk in ["a", "b", "c"] {
            rt_sha256_write(&[Value::Int(handle), Value::text(chunk.to_string()), Value::Int(1)]).unwrap();
        }
        assert_eq!(
            text_of(rt_sha256_finish(&[Value::Int(handle)]).unwrap()),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    /// A non-byte element must be a hard error, never a shortened hash.
    #[test]
    fn non_byte_element_errors() {
        let handle = new_handle();
        let arr = Value::Array(Arc::new(vec![Value::Int(1), Value::text("x".to_string())]));
        assert!(rt_sha256_write(&[Value::Int(handle), arr, Value::Int(2)]).is_err());
    }

    /// An out-of-range `len` must error rather than silently hash a prefix.
    #[test]
    fn overlong_len_errors() {
        let handle = new_handle();
        assert!(rt_sha256_write(&[Value::Int(handle), Value::text("abc".to_string()), Value::Int(9999)]).is_err());
    }

    /// An unknown handle must error, not return a digest of nothing. Guards
    /// against the "unregistered extern silently returns nil" family.
    #[test]
    fn unknown_handle_errors_rather_than_hashing_empty() {
        assert!(rt_sha256_finish(&[Value::Int(-424242)]).is_err());
        assert!(rt_sha256_write(&[Value::Int(-424242), Value::text("x".to_string()), Value::Int(1)]).is_err());
    }

    /// Reset must discard prior input.
    #[test]
    fn reset_discards_prior_input() {
        let handle = new_handle();
        rt_sha256_write(&[Value::Int(handle), Value::text("garbage".to_string()), Value::Int(7)]).unwrap();
        rt_sha256_reset(&[Value::Int(handle)]).unwrap();
        rt_sha256_write(&[Value::Int(handle), Value::text("abc".to_string()), Value::Int(3)]).unwrap();
        assert_eq!(
            text_of(rt_sha256_finish(&[Value::Int(handle)]).unwrap()),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    /// Free must release the handle; a later finish then errors.
    #[test]
    fn free_releases_handle() {
        let handle = new_handle();
        rt_sha256_free(&[Value::Int(handle)]).unwrap();
        assert!(rt_sha256_finish(&[Value::Int(handle)]).is_err());
        // Idempotent.
        rt_sha256_free(&[Value::Int(handle)]).unwrap();
    }

    /// Interleaved handles must not share state.
    #[test]
    fn concurrent_handles_are_independent() {
        let a = new_handle();
        let b = new_handle();
        rt_sha256_write(&[Value::Int(a), Value::text("a".to_string()), Value::Int(1)]).unwrap();
        rt_sha256_write(&[Value::Int(b), Value::text("abc".to_string()), Value::Int(3)]).unwrap();
        rt_sha256_write(&[Value::Int(a), Value::text("bc".to_string()), Value::Int(2)]).unwrap();
        let da = text_of(rt_sha256_finish(&[Value::Int(a)]).unwrap());
        let db = text_of(rt_sha256_finish(&[Value::Int(b)]).unwrap());
        assert_eq!(da, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(da, db);
    }
}
