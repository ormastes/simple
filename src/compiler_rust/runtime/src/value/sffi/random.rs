//! Random number generation SFFI.

use std::io::Read;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

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
    let mut hex = vec![0u8; n * 2];
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for (idx, byte) in bytes.iter().enumerate() {
        hex[idx * 2] = DIGITS[(byte >> 4) as usize];
        hex[idx * 2 + 1] = DIGITS[(byte & 0x0f) as usize];
    }
    unsafe { crate::value::collections::rt_string_new(hex.as_ptr(), hex.len() as u64) }
}

fn fill_random_bytes(buf: &mut [u8]) -> std::io::Result<()> {
    let mut file = std::fs::File::open("/dev/urandom")?;
    file.read_exact(buf)
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
}
