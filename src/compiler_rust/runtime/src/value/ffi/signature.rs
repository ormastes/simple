//! RSA-SHA256 and Ed25519 signature verification for SSH host keys.
//!
//! Used by SimpleOS SSH to verify server host key signatures during
//! the SSH handshake.  Both functions follow the same `[u8]` extraction
//! pattern as `ws_mask.rs`.

use crate::value::RuntimeValue;
use ring::signature::{UnparsedPublicKey, ED25519, RSA_PKCS1_2048_8192_SHA256};

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Public FFI exports
// ---------------------------------------------------------------------------

/// Verify an RSA-PKCS1 SHA-256 signature.
///
/// # Arguments
/// * `pubkey`    — `[u8]` DER-encoded RSA public key (SubjectPublicKeyInfo)
/// * `message`   — `[u8]` message bytes that were signed
/// * `signature` — `[u8]` raw PKCS#1 v1.5 signature bytes
///
/// # Returns
/// `1` if the signature is valid, `0` otherwise (including on any error).
#[no_mangle]
pub extern "C" fn rt_rsa_sha256_verify(
    pubkey: RuntimeValue,
    message: RuntimeValue,
    signature: RuntimeValue,
) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// Verify an Ed25519 signature.
///
/// # Arguments
/// * `pubkey`    — `[u8]` 32-byte Ed25519 public key
/// * `message`   — `[u8]` message bytes that were signed
/// * `signature` — `[u8]` 64-byte Ed25519 signature
///
/// # Returns
/// `1` if the signature is valid, `0` otherwise (including on any error).
#[no_mangle]
pub extern "C" fn rt_ed25519_verify(
    pubkey: RuntimeValue,
    message: RuntimeValue,
    signature: RuntimeValue,
) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&ED25519, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}
