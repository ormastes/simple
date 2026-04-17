//! RSA / Ed25519 / ECDSA-P256 signature primitives for SSH host keys.
//!
//! Used by SimpleOS SSH to verify peer signatures and to sign KEX
//! exchange hashes with the server host key during the SSH handshake
//! (RFC 4253, RFC 5656, RFC 8332).  Inputs are extracted from Simple
//! `[u8]` arrays via `runtime_byte_array_to_vec`; byte-array outputs
//! are returned through `rt_string_new` (Simple text and `[u8]` share
//! the same internal representation).

use crate::value::RuntimeValue;
use ring::rand::SystemRandom;
use ring::signature::{
    EcdsaKeyPair, KeyPair, RsaKeyPair, UnparsedPublicKey, ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA256_FIXED_SIGNING,
    ED25519, RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_2048_8192_SHA512, RSA_PKCS1_SHA256, RSA_PKCS1_SHA512,
    RSA_PSS_2048_8192_SHA256, RSA_PSS_2048_8192_SHA384, RSA_PSS_2048_8192_SHA512,
};

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

fn der_read_length(data: &[u8], offset: usize) -> Option<(usize, usize)> {
    let first = *data.get(offset)?;
    if first < 0x80 {
        return Some((first as usize, 1));
    }
    match first {
        0x81 => Some((*data.get(offset + 1)? as usize, 2)),
        0x82 => {
            let hi = *data.get(offset + 1)? as usize;
            let lo = *data.get(offset + 2)? as usize;
            Some(((hi << 8) | lo, 3))
        }
        _ => None,
    }
}

fn der_read_tlv(data: &[u8], offset: usize) -> Option<(u8, usize, usize, usize)> {
    let tag = *data.get(offset)?;
    let (value_len, len_header_size) = der_read_length(data, offset + 1)?;
    let value_offset = offset + 1 + len_header_size;
    let total_len = 1 + len_header_size + value_len;
    if value_offset + value_len > data.len() {
        return None;
    }
    Some((tag, value_offset, value_len, total_len))
}

fn is_pkcs1_rsa_public_key_der(data: &[u8]) -> bool {
    let Some((tag, value_offset, value_len, total_len)) = der_read_tlv(data, 0) else {
        return false;
    };
    if tag != 0x30 || total_len != data.len() {
        return false;
    }
    let seq_end = value_offset + value_len;
    let Some((n_tag, _, _, n_total_len)) = der_read_tlv(data, value_offset) else {
        return false;
    };
    if n_tag != 0x02 {
        return false;
    }
    let e_offset = value_offset + n_total_len;
    let Some((e_tag, _, _, e_total_len)) = der_read_tlv(data, e_offset) else {
        return false;
    };
    if e_tag != 0x02 {
        return false;
    }
    e_offset + e_total_len == seq_end
}

fn normalize_rsa_public_key(pubkey: &[u8]) -> Option<Vec<u8>> {
    if is_pkcs1_rsa_public_key_der(pubkey) {
        return Some(pubkey.to_vec());
    }

    let (outer_tag, outer_value_offset, outer_value_len, outer_total_len) = der_read_tlv(pubkey, 0)?;
    if outer_tag != 0x30 || outer_total_len != pubkey.len() {
        return None;
    }

    let outer_end = outer_value_offset + outer_value_len;
    let (_, _, _, alg_total_len) = der_read_tlv(pubkey, outer_value_offset)?;
    let bit_string_offset = outer_value_offset + alg_total_len;
    let (bit_tag, bit_value_offset, bit_value_len, bit_total_len) = der_read_tlv(pubkey, bit_string_offset)?;
    if bit_tag != 0x03 || bit_string_offset + bit_total_len != outer_end || bit_value_len < 1 {
        return None;
    }
    if pubkey[bit_value_offset] != 0 {
        return None;
    }

    let inner = &pubkey[(bit_value_offset + 1)..(bit_value_offset + bit_value_len)];
    if !is_pkcs1_rsa_public_key_der(inner) {
        return None;
    }
    Some(inner.to_vec())
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
pub extern "C" fn rt_rsa_sha256_verify(pubkey: RuntimeValue, message: RuntimeValue, signature: RuntimeValue) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(pk_bytes) = normalize_rsa_public_key(&pk_bytes) else {
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
pub extern "C" fn rt_ed25519_verify(pubkey: RuntimeValue, message: RuntimeValue, signature: RuntimeValue) -> i64 {
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

/// Verify an RSA-PKCS1 SHA-512 signature (RFC 8332 `rsa-sha2-512`).
///
/// Mirror of `rt_rsa_sha256_verify`; see that function's docs.
#[no_mangle]
pub extern "C" fn rt_rsa_sha512_verify(pubkey: RuntimeValue, message: RuntimeValue, signature: RuntimeValue) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(pk_bytes) = normalize_rsa_public_key(&pk_bytes) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA512, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

// === RSA-PSS Verify ===
//
// Three functions for RSA-PSS (RSASSA-PSS) used in TLS 1.3 certificate
// verification.  The pubkey is SPKI DER (same format as the PKCS#1 verify
// functions above).  Each returns 1 on valid, 0 on any error.

/// Verify an RSA-PSS SHA-256 signature (TLS 1.3 `rsa_pss_rsae_sha256`).
///
/// # Arguments
/// * `pubkey`    — `[u8]` DER-encoded RSA public key (SubjectPublicKeyInfo)
/// * `message`   — `[u8]` message bytes that were signed
/// * `signature` — `[u8]` raw RSA-PSS signature bytes
///
/// # Returns
/// `1` if the signature is valid, `0` otherwise (including on any error).
#[no_mangle]
pub extern "C" fn rt_rsa_pss_sha256_verify(
    pubkey: RuntimeValue,
    message: RuntimeValue,
    signature: RuntimeValue,
) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(pk_bytes) = normalize_rsa_public_key(&pk_bytes) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&RSA_PSS_2048_8192_SHA256, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// Verify an RSA-PSS SHA-384 signature (TLS 1.3 `rsa_pss_rsae_sha384`).
///
/// Mirror of `rt_rsa_pss_sha256_verify`; see that function's docs.
#[no_mangle]
pub extern "C" fn rt_rsa_pss_sha384_verify(
    pubkey: RuntimeValue,
    message: RuntimeValue,
    signature: RuntimeValue,
) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(pk_bytes) = normalize_rsa_public_key(&pk_bytes) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&RSA_PSS_2048_8192_SHA384, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// Verify an RSA-PSS SHA-512 signature (TLS 1.3 `rsa_pss_rsae_sha512`).
///
/// Mirror of `rt_rsa_pss_sha256_verify`; see that function's docs.
#[no_mangle]
pub extern "C" fn rt_rsa_pss_sha512_verify(
    pubkey: RuntimeValue,
    message: RuntimeValue,
    signature: RuntimeValue,
) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(pk_bytes) = normalize_rsa_public_key(&pk_bytes) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&RSA_PSS_2048_8192_SHA512, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// Verify an ECDSA P-256 SHA-256 fixed-width signature (RFC 5656
/// `ecdsa-sha2-nistp256` raw `r‖s`, 64 bytes).
///
/// The SSH wire format carries `mpint r + mpint s`; the Simple-side
/// wrapper unpacks that to fixed-width 64-byte form before calling
/// this extern.
#[no_mangle]
pub extern "C" fn rt_ecdsa_p256_verify(pubkey: RuntimeValue, message: RuntimeValue, signature: RuntimeValue) -> i64 {
    let Some(pk_bytes) = runtime_byte_array_to_vec(pubkey) else {
        return 0;
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return 0;
    };
    let Some(sig_bytes) = runtime_byte_array_to_vec(signature) else {
        return 0;
    };

    let key = UnparsedPublicKey::new(&ECDSA_P256_SHA256_FIXED, pk_bytes);
    match key.verify(&msg_bytes, &sig_bytes) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

fn _empty_bytes() -> RuntimeValue {
    // Return an empty `[u8]` so Simple callers can uniformly check
    // `len() == 0` for errors (returning NIL would surface as an i64
    // and break `.len()` dispatch in the interpreter).
    unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) }
}

// ---------------------------------------------------------------------------
// Signing
//
// All sign externs take PKCS#8 v1 DER private keys and return the raw
// signature bytes as a Simple `[u8]`, or `RuntimeValue::NIL` on any
// error (malformed key, message too big, ring error).  Hosted-only:
// all three sign paths require `SystemRandom` and will error on
// baremetal.
// ---------------------------------------------------------------------------

fn rsa_sign_impl(
    pkcs8: RuntimeValue,
    message: RuntimeValue,
    enc: &'static dyn ring::signature::RsaEncoding,
) -> RuntimeValue {
    let Some(key_bytes) = runtime_byte_array_to_vec(pkcs8) else {
        return _empty_bytes();
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return _empty_bytes();
    };

    let Ok(keypair) = RsaKeyPair::from_pkcs8(&key_bytes) else {
        return _empty_bytes();
    };

    let rng = SystemRandom::new();
    let mut signature = vec![0u8; keypair.public().modulus_len()];
    if keypair.sign(enc, &rng, &msg_bytes, &mut signature).is_err() {
        return _empty_bytes();
    }
    unsafe { crate::value::collections::rt_string_new(signature.as_ptr(), signature.len() as u64) }
}

/// Sign `message` with RSA-PKCS1 SHA-256 using a PKCS#8-v1 DER private
/// key (RFC 8332 `rsa-sha2-256`).
///
/// # Returns
/// Signature bytes (`key_modulus_len` bytes) on success; `NIL` on any
/// error (malformed PKCS#8, non-RSA key, key below ring's 2048-bit
/// minimum, RNG failure).
///
/// Determinism: PKCS#1 v1.5 produces byte-identical output for the
/// same `(key, message)` pair.
///
/// Hosted-only: requires `ring::rand::SystemRandom`.
#[no_mangle]
pub extern "C" fn rt_rsa_sha256_sign(pkcs8: RuntimeValue, message: RuntimeValue) -> RuntimeValue {
    rsa_sign_impl(pkcs8, message, &RSA_PKCS1_SHA256)
}

/// Sign `message` with RSA-PKCS1 SHA-512 using a PKCS#8-v1 DER private
/// key (RFC 8332 `rsa-sha2-512`).
///
/// Mirror of `rt_rsa_sha256_sign`.
#[no_mangle]
pub extern "C" fn rt_rsa_sha512_sign(pkcs8: RuntimeValue, message: RuntimeValue) -> RuntimeValue {
    rsa_sign_impl(pkcs8, message, &RSA_PKCS1_SHA512)
}

/// Sign `message` with Ed25519 using a PKCS#8-v1 DER private key
/// (RFC 8032 EdDSA, `ssh-ed25519`).
///
/// Output is the 64-byte raw Ed25519 signature.
///
/// Deterministic per RFC 8032 (no random nonce).
///
/// Hosted-only: requires `ring::signature::Ed25519KeyPair`.
#[no_mangle]
pub extern "C" fn rt_ed25519_sign(pkcs8: RuntimeValue, message: RuntimeValue) -> RuntimeValue {
    let Some(key_bytes) = runtime_byte_array_to_vec(pkcs8) else {
        return _empty_bytes();
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return _empty_bytes();
    };

    let keypair = match ring::signature::Ed25519KeyPair::from_pkcs8(&key_bytes) {
        Ok(kp) => kp,
        Err(_) => return _empty_bytes(),
    };

    let sig = keypair.sign(&msg_bytes);
    let bytes = sig.as_ref();
    unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
}

/// Sign `message` with ECDSA P-256 SHA-256 using a PKCS#8-v1 DER
/// private key (RFC 5656 `ecdsa-sha2-nistp256`).
///
/// Output is fixed-width 64-byte `r‖s`; the SSH wire wrapper converts
/// this to `mpint r + mpint s` format on the Simple side.
///
/// Non-deterministic: signature bytes differ per call by design.
///
/// Hosted-only: requires `ring::rand::SystemRandom`.
#[no_mangle]
pub extern "C" fn rt_ecdsa_p256_sign(pkcs8: RuntimeValue, message: RuntimeValue) -> RuntimeValue {
    let Some(key_bytes) = runtime_byte_array_to_vec(pkcs8) else {
        return _empty_bytes();
    };
    let Some(msg_bytes) = runtime_byte_array_to_vec(message) else {
        return _empty_bytes();
    };

    let rng = SystemRandom::new();
    let Ok(keypair) = EcdsaKeyPair::from_pkcs8(&ECDSA_P256_SHA256_FIXED_SIGNING, &key_bytes, &rng) else {
        return _empty_bytes();
    };

    let Ok(sig) = keypair.sign(&rng, &msg_bytes) else {
        return _empty_bytes();
    };
    let bytes = sig.as_ref();
    unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
}
