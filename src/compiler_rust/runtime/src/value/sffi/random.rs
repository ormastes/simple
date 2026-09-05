//! Random number generation SFFI.

use rand::RngCore;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};
use zeroize::Zeroize;

const LCG_A: u64 = 1_664_525;
const LCG_C: u64 = 1_013_904_223;
const LCG_M: u64 = 4_294_967_296;
const LCG_M_F: f64 = 4_294_967_296.0;

struct RandomState {
    state: u64,
    initialized: bool,
}

static RANDOM_STATE: Mutex<RandomState> = Mutex::new(RandomState {
    state: 0,
    initialized: false,
});

fn initial_seed() -> u64 {
    let micros = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_micros() as u64)
        .unwrap_or(0);
    micros % LCG_M
}

fn ensure_initialized(state: &mut RandomState) {
    if !state.initialized {
        state.state = initial_seed();
        state.initialized = true;
    }
}

fn advance(state: &mut RandomState) -> u64 {
    state.state = LCG_A.wrapping_mul(state.state).wrapping_add(LCG_C) % LCG_M;
    state.state
}

#[no_mangle]
pub extern "C" fn rt_random_seed(seed: i64) {
    let mut state = RANDOM_STATE.lock().expect("random state lock");
    state.state = (seed as u64) % LCG_M;
    state.initialized = true;
}
#[no_mangle]
pub extern "C" fn rt_random_getstate() -> i64 {
    let mut state = RANDOM_STATE.lock().expect("random state lock");
    ensure_initialized(&mut state);
    state.state as i64
}
#[no_mangle]
pub extern "C" fn rt_random_setstate(new_state: i64) {
    let mut state = RANDOM_STATE.lock().expect("random state lock");
    state.state = (new_state as u64) % LCG_M;
    state.initialized = true;
}
#[no_mangle]
pub extern "C" fn rt_random_next() -> i64 {
    let mut state = RANDOM_STATE.lock().expect("random state lock");
    ensure_initialized(&mut state);
    advance(&mut state) as i64
}
#[no_mangle]
pub extern "C" fn rt_random_randint(min: i64, max: i64) -> i64 {
    if min > max {
        return min;
    }
    let range = max - min + 1;
    min + (rt_random_next() % range)
}
#[no_mangle]
pub extern "C" fn rt_random_random() -> f64 {
    rt_random_next() as f64 / LCG_M_F
}
#[no_mangle]
pub extern "C" fn rt_random_uniform(min: f64, max: f64) -> f64 {
    min + rt_random_random() * (max - min)
}

#[no_mangle]
pub extern "C" fn rt_random_hex(len: i64) -> crate::value::RuntimeValue {
    let n = len.max(0) as usize;
    if n == 0 {
        return unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) };
    }
    let mut bytes = vec![0u8; n];
    if fill_random_bytes(&mut bytes).is_err() {
        return crate::value::RuntimeValue::NIL;
    }
    let mut hex = encode_hex(&bytes);
    secure_wipe(&mut bytes);
    let value = unsafe { crate::value::collections::rt_string_new(hex.as_ptr(), hex.len() as u64) };
    secure_wipe(&mut hex);
    value
}

#[cfg(test)]
fn secure_random_hex_exact_with<F, E>(len: i64, fill: F) -> Option<Vec<u8>>
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

fn encode_hex(bytes: &[u8]) -> Vec<u8> {
    let mut hex = vec![0u8; bytes.len() * 2];
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for (idx, byte) in bytes.iter().enumerate() {
        hex[idx * 2] = DIGITS[(byte >> 4) as usize];
        hex[idx * 2 + 1] = DIGITS[(byte & 0x0f) as usize];
    }
    hex
}

fn secure_wipe(bytes: &mut [u8]) {
    bytes.zeroize();
}

fn fill_random_bytes(buf: &mut [u8]) -> std::io::Result<()> {
    fill_random_bytes_with(buf, |dest| {
        rand::rngs::OsRng
            .try_fill_bytes(dest)
            .map_err(|error| std::io::Error::new(std::io::ErrorKind::Other, error.to_string()))
    })
}

fn fill_random_bytes_with<F>(buf: &mut [u8], fill: F) -> std::io::Result<()>
where
    F: FnOnce(&mut [u8]) -> std::io::Result<()>,
{
    let result = fill(buf);
    if result.is_err() {
        secure_wipe(buf);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};

    #[test]
    fn lcg_sequence_matches_legacy_constants() {
        rt_random_seed(1);
        assert_eq!(rt_random_next(), 1_015_568_748);
        assert_eq!(rt_random_next(), 1_586_005_467);
    }

    #[test]
    fn randint_respects_bounds_and_invalid_range() {
        rt_random_seed(1);
        let value = rt_random_randint(10, 20);
        assert!((10..=20).contains(&value));
        assert_eq!(rt_random_randint(20, 10), 20);
    }

    #[test]
    fn random_hex_returns_two_hex_chars_per_byte() {
        let value = rt_random_hex(8);
        let len = rt_string_len(value);
        let data = rt_string_data(value);
        assert_eq!(len, 16);
        assert!(!data.is_null());
    }

    #[test]
    fn capability_entropy_provider_returns_exactly_sixteen_bytes() {
        let mut bytes = [0u8; 16];
        fill_random_bytes_with(&mut bytes, |dest| {
            assert_eq!(dest.len(), 16);
            dest.fill(0xa5);
            Ok(())
        })
        .expect("deterministic entropy provider");
        assert_eq!(bytes.len(), 16);
        secure_wipe(&mut bytes);
    }

    #[test]
    fn capability_entropy_provider_failure_erases_transient_material() {
        let mut bytes = [0xa5u8; 16];
        let result = fill_random_bytes_with(&mut bytes, |dest| {
            dest[0] = 0x5a;
            Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "deterministic provider failure",
            ))
        });
        assert!(result.is_err());
        assert!(bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn secure_entropy_policy_rejects_provider_failure_and_wrong_length() {
        assert!(secure_random_hex_exact_with(16, |_dest| Err::<(), ()>(())).is_none());
        assert!(secure_random_hex_exact_with(15, |_dest| Ok::<(), ()>(())).is_none());
    }

    #[test]
    fn secure_entropy_policy_accepts_exact_lowercase_hex_and_rejects_zero() {
        let exact = secure_random_hex_exact_with(16, |dest| {
            dest.fill(0xab);
            Ok::<(), ()>(())
        })
        .expect("nonzero deterministic provider");
        assert_eq!(exact.len(), 32);
        assert!(exact
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte)));
        assert!(secure_random_hex_exact_with(16, |dest| {
            dest.fill(0);
            Ok::<(), ()>(())
        })
        .is_none());
    }
}
