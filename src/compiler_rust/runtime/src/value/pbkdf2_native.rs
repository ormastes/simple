//! Native PBKDF2-HMAC-SHA-2 helpers backed by the RustCrypto `pbkdf2`
//! and `hmac` crates.
//!
//! These functions exist so that the interpreter (`bin/simple test`) can
//! short-circuit the pure-Simple PBKDF2 inner loop in
//! `src/lib/common/crypto/pbkdf2.spl` for high-iteration test vectors
//! (RFC 6070 c=4096, draft-josefsson c=80000) which otherwise blow past
//! the 60 s test-runner watchdog.
//!
//! The pure-Simple implementation remains the canonical reference and
//! the fallback path when the extern is unavailable (early bootstrap
//! stages, baremetal targets); the helpers here are byte-exact with it
//! and with `hashlib.pbkdf2_hmac("sha256"/"sha384"/"sha512", ...)`.
//!
//! See: `doc/02_requirements/feature/pbkdf2_native_runtime_helpers_2026-05-01.md`.

use hmac::Hmac;
use sha1::Sha1;
use sha2::{Sha256, Sha384, Sha512};

/// PBKDF2-HMAC-SHA-1 (RFC 5802 SCRAM-SHA-1).
///
/// Returns a freshly-allocated `Vec<u8>` of length `dk_len`.
/// `iterations` and `dk_len` are clamped to non-negative `u32` /
/// `usize` respectively; `iterations <= 0` is normalised to 1 to match
/// the existing pure-Simple semantics for defensive callers.
pub fn pbkdf2_hmac_sha1(password: &[u8], salt: &[u8], iterations: i64, dk_len: i64) -> Vec<u8> {
    let rounds = if iterations <= 0 {
        1u32
    } else {
        iterations.min(u32::MAX as i64) as u32
    };
    let n = if dk_len <= 0 { 0usize } else { dk_len as usize };
    let mut out = vec![0u8; n];
    if n > 0 {
        pbkdf2::pbkdf2::<Hmac<Sha1>>(password, salt, rounds, &mut out);
    }
    out
}

/// PBKDF2-HMAC-SHA-256.
///
/// Returns a freshly-allocated `Vec<u8>` of length `dk_len`.
/// `iterations` and `dk_len` are clamped to non-negative `u32` /
/// `usize` respectively; `iterations <= 0` is normalised to 1 to match
/// the existing pure-Simple semantics for defensive callers.
pub fn pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: i64, dk_len: i64) -> Vec<u8> {
    let rounds = if iterations <= 0 {
        1u32
    } else {
        iterations.min(u32::MAX as i64) as u32
    };
    let n = if dk_len <= 0 { 0usize } else { dk_len as usize };
    let mut out = vec![0u8; n];
    if n > 0 {
        pbkdf2::pbkdf2::<Hmac<Sha256>>(password, salt, rounds, &mut out);
    }
    out
}

/// PBKDF2-HMAC-SHA-384.
pub fn pbkdf2_hmac_sha384(password: &[u8], salt: &[u8], iterations: i64, dk_len: i64) -> Vec<u8> {
    let rounds = if iterations <= 0 {
        1u32
    } else {
        iterations.min(u32::MAX as i64) as u32
    };
    let n = if dk_len <= 0 { 0usize } else { dk_len as usize };
    let mut out = vec![0u8; n];
    if n > 0 {
        pbkdf2::pbkdf2::<Hmac<Sha384>>(password, salt, rounds, &mut out);
    }
    out
}

/// PBKDF2-HMAC-SHA-512.
pub fn pbkdf2_hmac_sha512(password: &[u8], salt: &[u8], iterations: i64, dk_len: i64) -> Vec<u8> {
    let rounds = if iterations <= 0 {
        1u32
    } else {
        iterations.min(u32::MAX as i64) as u32
    };
    let n = if dk_len <= 0 { 0usize } else { dk_len as usize };
    let mut out = vec![0u8; n];
    if n > 0 {
        pbkdf2::pbkdf2::<Hmac<Sha512>>(password, salt, rounds, &mut out);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(bytes: &[u8]) -> String {
        let mut s = String::with_capacity(bytes.len() * 2);
        for b in bytes {
            s.push_str(&format!("{:02x}", b));
        }
        s
    }

    // RFC 6070 §2 TC1: P="password" S="salt" c=1 dkLen=20
    #[test]
    fn rfc6070_tc1_sha256_extended() {
        // Not in RFC 6070 (which is SHA-1) but matches draft-josefsson §2 TC1
        let dk = pbkdf2_hmac_sha256(b"password", b"salt", 1, 32);
        assert_eq!(
            hex(&dk),
            "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b"
        );
    }

    #[test]
    fn rfc6070_tc2_sha256_extended() {
        let dk = pbkdf2_hmac_sha256(b"password", b"salt", 2, 32);
        assert_eq!(
            hex(&dk),
            "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43"
        );
    }

    // draft-josefsson-pbkdf2-test-vectors-00 §2 TC3
    #[test]
    fn josefsson_tc3_sha256_c4096() {
        let dk = pbkdf2_hmac_sha256(b"password", b"salt", 4096, 32);
        assert_eq!(
            hex(&dk),
            "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a"
        );
    }

    // draft-josefsson-pbkdf2-test-vectors-00 §3 TC1
    #[test]
    fn josefsson_tc1_sha512_c1() {
        let dk = pbkdf2_hmac_sha512(b"password", b"salt", 1, 64);
        assert_eq!(
            hex(&dk),
            "867f70cf1ade02cff3752599a3a53dc4af34c7a669815ae5d513554e1c8cf252\
             c02d470a285a0501bad999bfe943c08f050235d7d68b1da55e63f73b60a57fce"
        );
    }

    // PBKDF2-HMAC-SHA-384 cross-checked against
    // hashlib.pbkdf2_hmac("sha384", b"password", b"salt", 1, 48)
    #[test]
    fn sha384_c1_dk48() {
        let dk = pbkdf2_hmac_sha384(b"password", b"salt", 1, 48);
        assert_eq!(
            hex(&dk),
            "c0e14f06e49e32d73f9f52ddf1d0c5c7191609233631dadd76a567db42b78676\
             b38fc800cc53ddb642f5c74442e62be4"
        );
    }

    #[test]
    fn dk_len_zero() {
        let dk = pbkdf2_hmac_sha256(b"password", b"salt", 1, 0);
        assert!(dk.is_empty());
    }

    // RFC 6070 §2 TC1: P="password" S="salt" c=4096 dkLen=20 (SHA-1)
    #[test]
    fn rfc6070_tc3_sha1_c4096() {
        let dk = pbkdf2_hmac_sha1(b"password", b"salt", 4096, 20);
        assert_eq!(
            hex(&dk),
            "4b007901b765489abead49d926f721d065a429c1"
        );
    }
}
