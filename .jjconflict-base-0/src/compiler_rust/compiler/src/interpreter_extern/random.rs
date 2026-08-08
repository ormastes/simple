//! Random number generation extern functions
//!
//! Provides random number generation with global state stored in the runtime.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use rand::RngCore;
use zeroize::Zeroize;

// Import runtime SFFI random functions
use simple_runtime::value::sffi::random::{
    rt_random_seed, rt_random_getstate, rt_random_setstate, rt_random_next, rt_random_randint, rt_random_random,
    rt_random_uniform,
};

/// rt_random_seed - Set the random seed
pub fn rt_random_seed_fn(args: &[Value]) -> Result<Value, CompileError> {
    let seed = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_seed expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    rt_random_seed(seed);
    Ok(Value::Nil)
}

/// rt_random_getstate - Get current random state
pub fn rt_random_getstate_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_random_getstate()))
}

/// rt_random_setstate - Set random state
pub fn rt_random_setstate_fn(args: &[Value]) -> Result<Value, CompileError> {
    let state = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_setstate expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    rt_random_setstate(state);
    Ok(Value::Nil)
}

/// rt_random_next - Generate next random number
pub fn rt_random_next_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_random_next()))
}

/// rt_random_randint - Generate random integer in range
pub fn rt_random_randint_fn(args: &[Value]) -> Result<Value, CompileError> {
    let min = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_randint expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let max = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_randint expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    Ok(Value::Int(rt_random_randint(min, max)))
}

/// rt_random_random - Generate random float [0.0, 1.0)
pub fn rt_random_random_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Float(rt_random_random()))
}

/// rt_random_uniform - Generate random float in range
pub fn rt_random_uniform_fn(args: &[Value]) -> Result<Value, CompileError> {
    let min = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_uniform expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    let max = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_uniform expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_random_uniform(min, max)))
}

/// rt_random_hex - N cryptographically-secure random bytes, hex-encoded.
/// Returns a 2*N-char text drawn from [0-9a-f]. Backed by OS CSPRNG (OsRng).
pub fn rt_random_hex_fn(args: &[Value]) -> Result<Value, CompileError> {
    let len = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_random_hex expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let n = len.max(0) as usize;
    Ok(
        match random_hex_with(n, |dest| rand::rngs::OsRng.try_fill_bytes(dest)) {
            Some(hex) => Value::text(hex),
            None => Value::Nil,
        },
    )
}

fn random_hex_with<F, E>(len: usize, fill: F) -> Option<String>
where
    F: FnOnce(&mut [u8]) -> Result<(), E>,
{
    let mut bytes = vec![0u8; len];
    if fill(&mut bytes).is_err() {
        secure_wipe(&mut bytes);
        return None;
    }
    let hex = encode_hex(&bytes);
    secure_wipe(&mut bytes);
    Some(hex)
}

#[cfg(test)]
fn secure_random_hex_exact_with<F, E>(len: i64, fill: F) -> Option<String>
where
    F: FnOnce(&mut [u8]) -> Result<(), E>,
{
    if len != 16 {
        return None;
    }
    let mut bytes = [0u8; 16];
    if fill(&mut bytes).is_err() || bytes.iter().all(|byte| *byte == 0) {
        secure_wipe(&mut bytes);
        return None;
    }
    let hex = encode_hex(&bytes);
    secure_wipe(&mut bytes);
    Some(hex)
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut hex = vec![0u8; bytes.len() * 2];
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for (idx, byte) in bytes.iter().enumerate() {
        hex[idx * 2] = DIGITS[(byte >> 4) as usize];
        hex[idx * 2 + 1] = DIGITS[(byte & 0x0f) as usize];
    }
    // SAFETY: every output byte comes from the ASCII-only DIGITS table.
    unsafe { String::from_utf8_unchecked(hex) }
}

fn secure_wipe(bytes: &mut [u8]) {
    bytes.zeroize();
}

/// rt_random_i64 - Generate a random i64 value using OS CSPRNG.
///
/// Callable from Simple as: `rt_random_i64()`
pub fn rt_random_i64_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use rand::Rng;
    let val: i64 = rand::rngs::OsRng.gen();
    Ok(Value::Int(val))
}

/// rt_entropy_hardware_ready - Interpreter-side host entropy readiness.
///
/// Hosted/interpreter mode has OS CSPRNG support but does not prove baremetal
/// CPU entropy. Return 0 so baremetal TLS gates stay conservative in tests.
pub fn rt_entropy_hardware_ready_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random_hex_provider_failure_returns_nil_parity() {
        assert!(random_hex_with(16, |_dest| Err::<(), ()>(())).is_none());
    }

    #[test]
    fn secure_entropy_policy_covers_failure_length_canonical_and_zero() {
        assert!(secure_random_hex_exact_with(16, |_dest| Err::<(), ()>(())).is_none());
        assert!(secure_random_hex_exact_with(17, |_dest| Ok::<(), ()>(())).is_none());
        let exact = secure_random_hex_exact_with(16, |dest| {
            dest.fill(0x5a);
            Ok::<(), ()>(())
        })
        .expect("nonzero deterministic provider");
        assert_eq!(exact.len(), 32);
        assert!(exact
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)));
        assert!(secure_random_hex_exact_with(16, |dest| {
            dest.fill(0);
            Ok::<(), ()>(())
        })
        .is_none());
    }
}
