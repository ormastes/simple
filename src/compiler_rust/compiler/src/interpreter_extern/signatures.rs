//! Interpreter-side handlers for signing externs.
//!
//! These mirror `src/compiler_rust/runtime/src/value/ffi/signature.rs` (the
//! native-code FFI) but return the interpreter's `Value::Array` directly,
//! so `bin/simple test` can execute `it` blocks that call the sign/verify
//! paths without going through `dynamic_ffi` (which marshals all extern
//! returns as `i64` and therefore can't round-trip `[u8]`).
//!
//! # Symbols
//! - `rt_rsa_sha256_sign` / `rt_rsa_sha512_sign`  — RFC 8332 PKCS#1 v1.5
//! - `rt_rsa_sha512_verify`                       — RFC 8332 PKCS#1 v1.5
//! - `rt_ecdsa_p256_sign` / `rt_ecdsa_p256_verify` — RFC 5656 SEC1 fixed r‖s
//!
//! # Error convention (kept in sync with runtime/signature.rs)
//! - Sign: returns `Value::Array(empty)` on any error (malformed PKCS#8,
//!   non-matching key type, ring error). Simple callers check `sig.len() > 0`.
//! - Verify: returns `Value::Int(0)` on mismatch or error; `Value::Int(1)` on OK.

use crate::error::CompileError;
use crate::value::Value;
use ring::rand::SystemRandom;
use ring::signature::{
    EcdsaKeyPair, KeyPair, RsaKeyPair, UnparsedPublicKey, ECDSA_P256_SHA256_FIXED,
    ECDSA_P256_SHA256_FIXED_SIGNING, ED25519, RSA_PKCS1_2048_8192_SHA256,
    RSA_PKCS1_2048_8192_SHA512, RSA_PKCS1_SHA256, RSA_PKCS1_SHA512,
};
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract a `Vec<u8>` from a `Value::Array` of `Value::Int` entries.
/// Mirrors the `rt_sha1_write` byte-extraction pattern: `i as u8` truncates
/// to the low 8 bits so signed-wraparound byte values (e.g. i64(-128) for
/// 0x80) round-trip correctly. Returns None only if the arg is missing or
/// is not an Array.
fn extract_bytes(args: &[Value], index: usize) -> Option<Vec<u8>> {
    match args.get(index)? {
        Value::Array(arr) => Some(
            arr.iter()
                .filter_map(|v| match v {
                    Value::Int(i) => Some(*i as u8),
                    _ => None,
                })
                .collect(),
        ),
        _ => None,
    }
}

/// Wrap raw bytes in a `Value::Array(Arc<Vec<Value::Int(byte)>>)` shape
/// so Simple code sees a genuine `[u8]`.
fn bytes_to_value(bytes: &[u8]) -> Value {
    Value::Array(Arc::new(
        bytes.iter().map(|b| Value::Int(*b as i64)).collect(),
    ))
}

fn empty_bytes() -> Value {
    Value::Array(Arc::new(Vec::new()))
}

// ---------------------------------------------------------------------------
// RSA sign
// ---------------------------------------------------------------------------

fn rsa_sign_impl(
    args: &[Value],
    enc: &'static dyn ring::signature::RsaEncoding,
) -> Result<Value, CompileError> {
    let Some(pkcs8) = extract_bytes(args, 0) else {
        return Ok(empty_bytes());
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(empty_bytes());
    };
    let Ok(keypair) = RsaKeyPair::from_pkcs8(&pkcs8) else {
        return Ok(empty_bytes());
    };
    let rng = SystemRandom::new();
    let mut sig = vec![0u8; keypair.public().modulus_len()];
    if keypair.sign(enc, &rng, &msg, &mut sig).is_err() {
        return Ok(empty_bytes());
    }
    Ok(bytes_to_value(&sig))
}

/// `rt_rsa_sha256_sign(pkcs8: [u8], message: [u8]) -> [u8]`
pub fn rt_rsa_sha256_sign(args: &[Value]) -> Result<Value, CompileError> {
    rsa_sign_impl(args, &RSA_PKCS1_SHA256)
}

/// `rt_rsa_sha512_sign(pkcs8: [u8], message: [u8]) -> [u8]`
pub fn rt_rsa_sha512_sign(args: &[Value]) -> Result<Value, CompileError> {
    rsa_sign_impl(args, &RSA_PKCS1_SHA512)
}

// ---------------------------------------------------------------------------
// RSA verify
// ---------------------------------------------------------------------------

/// `rt_rsa_sha256_verify(spki: [u8], message: [u8], signature: [u8]) -> i64`
pub fn rt_rsa_sha256_verify(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pk) = extract_bytes(args, 0) else {
        return Ok(Value::Int(0));
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(Value::Int(0));
    };
    let Some(sig) = extract_bytes(args, 2) else {
        return Ok(Value::Int(0));
    };
    let key = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, pk);
    Ok(Value::Int(if key.verify(&msg, &sig).is_ok() {
        1
    } else {
        0
    }))
}

/// `rt_rsa_sha512_verify(spki: [u8], message: [u8], signature: [u8]) -> i64`
pub fn rt_rsa_sha512_verify(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pk) = extract_bytes(args, 0) else {
        return Ok(Value::Int(0));
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(Value::Int(0));
    };
    let Some(sig) = extract_bytes(args, 2) else {
        return Ok(Value::Int(0));
    };
    let key = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA512, pk);
    Ok(Value::Int(if key.verify(&msg, &sig).is_ok() {
        1
    } else {
        0
    }))
}

// ---------------------------------------------------------------------------
// Ed25519 verify
// ---------------------------------------------------------------------------

/// `rt_ed25519_verify(pubkey: [u8], message: [u8], signature: [u8]) -> i64`
pub fn rt_ed25519_verify(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pk) = extract_bytes(args, 0) else {
        return Ok(Value::Int(0));
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(Value::Int(0));
    };
    let Some(sig) = extract_bytes(args, 2) else {
        return Ok(Value::Int(0));
    };
    let key = UnparsedPublicKey::new(&ED25519, pk);
    Ok(Value::Int(if key.verify(&msg, &sig).is_ok() {
        1
    } else {
        0
    }))
}

// ---------------------------------------------------------------------------
// Ed25519 sign
// ---------------------------------------------------------------------------

/// `rt_ed25519_sign(pkcs8: [u8], message: [u8]) -> [u8]` (64-byte signature)
pub fn rt_ed25519_sign(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pkcs8) = extract_bytes(args, 0) else {
        return Ok(empty_bytes());
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(empty_bytes());
    };
    let keypair = match ring::signature::Ed25519KeyPair::from_pkcs8(&pkcs8) {
        Ok(kp) => kp,
        Err(_) => return Ok(empty_bytes()),
    };
    let sig = keypair.sign(&msg);
    Ok(bytes_to_value(sig.as_ref()))
}

// ---------------------------------------------------------------------------
// ECDSA P-256 sign / verify (fixed-width r‖s on the FFI boundary)
// ---------------------------------------------------------------------------

/// `rt_ecdsa_p256_sign(pkcs8: [u8], message: [u8]) -> [u8]` (64-byte r‖s)
pub fn rt_ecdsa_p256_sign(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pkcs8) = extract_bytes(args, 0) else {
        return Ok(empty_bytes());
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(empty_bytes());
    };
    let rng = SystemRandom::new();
    let Ok(keypair) = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, &pkcs8, &rng)
    else {
        return Ok(empty_bytes());
    };
    let Ok(sig) = keypair.sign(&rng, &msg) else {
        return Ok(empty_bytes());
    };
    Ok(bytes_to_value(sig.as_ref()))
}

/// `rt_ecdsa_p256_verify(spki: [u8], message: [u8], signature: [u8]) -> i64`
pub fn rt_ecdsa_p256_verify(args: &[Value]) -> Result<Value, CompileError> {
    let Some(pk) = extract_bytes(args, 0) else {
        return Ok(Value::Int(0));
    };
    let Some(msg) = extract_bytes(args, 1) else {
        return Ok(Value::Int(0));
    };
    let Some(sig) = extract_bytes(args, 2) else {
        return Ok(Value::Int(0));
    };
    let key = UnparsedPublicKey::new(&ECDSA_P256_SHA256_FIXED, pk);
    Ok(Value::Int(if key.verify(&msg, &sig).is_ok() {
        1
    } else {
        0
    }))
}
