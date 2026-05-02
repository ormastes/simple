/// SHA-512 interpreter dispatch (FIPS 180-4).
///
/// Implements the four `rt_sha512_*` externs declared in
/// `src/os/crypto/sha512.spl`:
///
/// - `rt_sha512_hash(data: [u8], unused: i64) -> i64` — computes SHA-512(data)
///   and stashes the 64-byte digest into a process-global single-slot buffer.
/// - `rt_sha512_byte(index: i64) -> i64` — returns the i-th byte (0..=63) of
///   the most recent `rt_sha512_hash` invocation.
/// - `rt_sha512_K(index: i64) -> u64` — FIPS 180-4 SHA-512 round constant
///   K[index] for index in 0..=79.
/// - `rt_sha512_H(index: i64) -> u64` — FIPS 180-4 SHA-512 initial hash value
///   H0[index] for index in 0..=7.
///
/// FR: doc/02_requirements/feature/sha512_interpreter_dispatch.md
/// Blocker for: W14-D (SLH-DSA-SHA2-{192s,256s}), HKDF-SHA-512,
/// HMAC-SHA-512, Ed25519 interpreter-mode coverage.
use crate::error::CompileError;
use crate::value::Value;
use ring::digest;
use std::sync::Mutex;

lazy_static::lazy_static! {
    /// Process-global single-slot buffer for the most recent SHA-512 digest.
    /// Mirrors the `static unsigned char` buffer used in the baremetal C-side
    /// `rt_sha512_byte` helper (see `examples/simple_os/arch/*/boot/`).
    static ref SHA512_LAST_DIGEST: Mutex<[u8; 64]> = Mutex::new([0u8; 64]);
}

/// FIPS 180-4 §4.2.3 SHA-512 round constants K[0..79].
/// First 64 bits of the fractional parts of the cube roots of the first 80
/// prime numbers.
const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

/// FIPS 180-4 §5.3.5 SHA-512 initial hash value H(0)[0..7].
/// First 64 bits of the fractional parts of the square roots of the first 8
/// prime numbers.
const SHA512_H: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

fn expect_byte_array(name: &str, value: &Value) -> Result<Vec<u8>, CompileError> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(byte) if (0..=255).contains(byte) => Ok(*byte as u8),
                Value::UInt { value, .. } if *value <= 255 => Ok(*value as u8),
                Value::Int(_) | Value::UInt { .. } => {
                    Err(CompileError::runtime(format!("{name} expects byte values in 0..255")))
                }
                _ => Err(CompileError::runtime(format!("{name} expects an array of integers"))),
            })
            .collect(),
        _ => Err(CompileError::runtime(format!("{name} expects an array argument"))),
    }
}

fn expect_index(name: &str, value: &Value, max_inclusive: i64) -> Result<i64, CompileError> {
    let n = match value {
        Value::Int(n) => *n,
        Value::UInt { value, .. } => *value as i64,
        _ => {
            return Err(CompileError::runtime(format!(
                "{name} expects a non-negative integer index"
            )))
        }
    };
    if n < 0 || n > max_inclusive {
        return Err(CompileError::runtime(format!(
            "{name} index {n} out of range 0..={max_inclusive}"
        )));
    }
    Ok(n)
}

/// `rt_sha512_hash(data: [u8], unused: i64) -> i64`
///
/// Computes SHA-512 of `data` and stores the 64-byte digest in the
/// process-global single-slot buffer. Returns 0 (matches the C-side
/// baremetal stub's "ignore the int, read the buffer" contract).
pub fn rt_sha512_hash(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "rt_sha512_hash expects at least 1 argument".to_string(),
        ));
    }
    let data = expect_byte_array("rt_sha512_hash", &args[0])?;
    let digest = digest::digest(&digest::SHA512, &data);
    let bytes = digest.as_ref();
    debug_assert_eq!(bytes.len(), 64);
    let mut slot = SHA512_LAST_DIGEST.lock().unwrap();
    slot.copy_from_slice(bytes);
    Ok(Value::Int(0))
}

/// `rt_sha512_byte(index: i64) -> i64`
///
/// Returns the `index`-th byte of the most recent `rt_sha512_hash`
/// invocation. `index` must be in 0..=63.
pub fn rt_sha512_byte(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_sha512_byte expects 1 argument".to_string()));
    }
    let idx = expect_index("rt_sha512_byte", &args[0], 63)? as usize;
    let slot = SHA512_LAST_DIGEST.lock().unwrap();
    Ok(Value::Int(slot[idx] as i64))
}

/// `rt_sha512_K(index: i64) -> u64`
///
/// Returns SHA-512 round constant K[index] for index in 0..=79.
pub fn rt_sha512_k(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_sha512_K expects 1 argument".to_string()));
    }
    let idx = expect_index("rt_sha512_K", &args[0], 79)? as usize;
    Ok(Value::UInt {
        value: SHA512_K[idx],
        width: 64,
    })
}

/// `rt_sha512_H(index: i64) -> u64`
///
/// Returns SHA-512 initial hash value H(0)[index] for index in 0..=7.
pub fn rt_sha512_h(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_sha512_H expects 1 argument".to_string()));
    }
    let idx = expect_index("rt_sha512_H", &args[0], 7)? as usize;
    Ok(Value::UInt {
        value: SHA512_H[idx],
        width: 64,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FIPS 180-4 Appendix C — "abc" SHA-512 digest.
    #[test]
    fn sha512_abc_vector() {
        let abc = Value::array(vec![Value::Int(0x61), Value::Int(0x62), Value::Int(0x63)]);
        let unused = Value::Int(0);
        rt_sha512_hash(&[abc, unused]).expect("hash ok");
        let expected: [u8; 64] = [
            0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73, 0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6,
            0xfa, 0x4e, 0x89, 0xa9, 0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21, 0x92, 0x99, 0x2a,
            0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23, 0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c,
            0xe8, 0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
        ];
        for i in 0..64 {
            let v = rt_sha512_byte(&[Value::Int(i as i64)]).expect("byte ok");
            match v {
                Value::Int(b) => assert_eq!(b as u8, expected[i], "mismatch at byte {i}"),
                _ => panic!("expected Int"),
            }
        }
    }

    #[test]
    fn sha512_k_first_and_last() {
        match rt_sha512_k(&[Value::Int(0)]).expect("K[0]") {
            Value::UInt { value, width } => {
                assert_eq!(width, 64);
                assert_eq!(value as u64, 0x428a2f98d728ae22u64);
            }
            _ => panic!("expected UInt"),
        }
        match rt_sha512_k(&[Value::Int(79)]).expect("K[79]") {
            Value::UInt { value, .. } => {
                assert_eq!(value as u64, 0x6c44198c4a475817u64);
            }
            _ => panic!("expected UInt"),
        }
    }

    #[test]
    fn sha512_h_first_and_last() {
        match rt_sha512_h(&[Value::Int(0)]).expect("H[0]") {
            Value::UInt { value, .. } => assert_eq!(value as u64, 0x6a09e667f3bcc908u64),
            _ => panic!("expected UInt"),
        }
        match rt_sha512_h(&[Value::Int(7)]).expect("H[7]") {
            Value::UInt { value, .. } => assert_eq!(value as u64, 0x5be0cd19137e2179u64),
            _ => panic!("expected UInt"),
        }
    }

    #[test]
    fn sha512_index_out_of_range() {
        assert!(rt_sha512_byte(&[Value::Int(64)]).is_err());
        assert!(rt_sha512_k(&[Value::Int(80)]).is_err());
        assert!(rt_sha512_h(&[Value::Int(8)]).is_err());
    }
}
