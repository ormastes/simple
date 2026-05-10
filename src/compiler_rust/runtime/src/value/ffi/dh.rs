//! Curve25519 Diffie-Hellman key exchange FFI.
//!
//! Provides ephemeral X25519 DH primitives for SSH key exchange (ECDH).
//! Uses `ring::agreement` for all cryptographic operations.
//!
//! ## Usage pattern (SSH KEX)
//! ```text
//! handle = rt_dh_curve25519_keypair()
//! my_pub = rt_dh_curve25519_public_key(handle)   // [u8; 32]
//! secret = rt_dh_curve25519_shared_secret(handle, their_pub)  // [u8; 32], consumes key
//! rt_dh_curve25519_free(handle)                  // no-op after shared_secret; safe to call
//! ```

use crate::value::RuntimeValue;
use ring::agreement::{self, EphemeralPrivateKey, PublicKey, UnparsedPublicKey, X25519};
use std::collections::HashMap;
use std::sync::Mutex;

struct Keypair {
    private_key: EphemeralPrivateKey,
    public_key_bytes: [u8; 32],
}

lazy_static::lazy_static! {
    static ref DH_MAP: Mutex<HashMap<i64, Keypair>> = Mutex::new(HashMap::new());
}

static DH_COUNTER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

/// Generate an ephemeral X25519 keypair and return an opaque handle.
///
/// Returns handle (> 0) on success, -1 on failure.
#[no_mangle]
pub extern "C" fn rt_dh_curve25519_keypair() -> i64 {
    let rng = ring::rand::SystemRandom::new();
    let private_key = match EphemeralPrivateKey::generate(&X25519, &rng) {
        Ok(k) => k,
        Err(_) => return -1,
    };
    let public_key: PublicKey = match private_key.compute_public_key() {
        Ok(k) => k,
        Err(_) => return -1,
    };
    let pub_bytes = public_key.as_ref();
    if pub_bytes.len() != 32 {
        return -1;
    }
    let mut arr = [0u8; 32];
    arr.copy_from_slice(pub_bytes);

    let handle = DH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    DH_MAP.lock().unwrap().insert(
        handle,
        Keypair {
            private_key,
            public_key_bytes: arr,
        },
    );
    handle
}

/// Return the public key bytes ([u8; 32]) as a RuntimeValue byte array.
///
/// Returns empty array if handle is invalid.
#[no_mangle]
pub extern "C" fn rt_dh_curve25519_public_key(handle: i64) -> RuntimeValue {
    let map = DH_MAP.lock().unwrap();
    match map.get(&handle) {
        Some(kp) => vec_to_runtime_byte_array(&kp.public_key_bytes),
        None => crate::value::collections::rt_array_new(0),
    }
}

/// Compute the shared secret from our private key and their public key.
///
/// `their_pub` must be a RuntimeValue byte array of exactly 32 bytes.
/// Consumes the private key (removes from store).
/// Returns [u8; 32] shared secret as a RuntimeValue byte array, or empty on error.
#[no_mangle]
pub extern "C" fn rt_dh_curve25519_shared_secret(handle: i64, their_pub: RuntimeValue) -> RuntimeValue {
    let their_bytes = match runtime_byte_array_to_vec(their_pub) {
        Some(v) if v.len() == 32 => v,
        _ => return crate::value::collections::rt_array_new(0),
    };

    let kp = {
        let mut map = DH_MAP.lock().unwrap();
        map.remove(&handle)
    };
    let kp = match kp {
        Some(k) => k,
        None => return crate::value::collections::rt_array_new(0),
    };

    let peer_pub = UnparsedPublicKey::new(&X25519, &their_bytes);
    let result = agreement::agree_ephemeral(kp.private_key, &peer_pub, |secret| {
        let mut out = [0u8; 32];
        out.copy_from_slice(secret);
        out
    });

    match result {
        Ok(secret) => vec_to_runtime_byte_array(&secret),
        Err(_) => crate::value::collections::rt_array_new(0),
    }
}

/// Free the keypair identified by `handle`.
///
/// Safe to call after `rt_dh_curve25519_shared_secret` (already removed) or
/// with an invalid handle.
#[no_mangle]
pub extern "C" fn rt_dh_curve25519_free(handle: i64) {
    DH_MAP.lock().unwrap().remove(&handle);
}

// ---------------------------------------------------------------------------
// Internal helpers (mirrors ws_mask.rs pattern)
// ---------------------------------------------------------------------------

fn runtime_byte_array_to_vec(data: RuntimeValue) -> Option<Vec<u8>> {
    let len = crate::value::collections::rt_array_len(data);
    if len < 0 {
        return None;
    }
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        let v = crate::value::collections::rt_array_get(data, i);
        if !v.is_int() {
            return None;
        }
        let byte = v.as_int();
        if !(0..=255).contains(&byte) {
            return None;
        }
        out.push(byte as u8);
    }
    Some(out)
}

fn vec_to_runtime_byte_array(bytes: &[u8]) -> RuntimeValue {
    let array = crate::value::collections::rt_array_new(bytes.len() as u64);
    for &b in bytes {
        let val = RuntimeValue::from_int(b as i64);
        crate::value::collections::rt_array_push(array, val);
    }
    array
}
