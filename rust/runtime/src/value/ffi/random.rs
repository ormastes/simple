//! Random number generation FFI for Simple language.
//!
//! Provides thread-safe random number generation with global state
//! managed in the runtime. Uses a Linear Congruential Generator (LCG)
//! with parameters from Numerical Recipes.

use std::sync::RwLock;
use std::time::{SystemTime, UNIX_EPOCH};

/// Global random state protected by RwLock
static GLOBAL_RNG_STATE: RwLock<Option<i64>> = RwLock::new(None);

// LCG parameters from Numerical Recipes
const LCG_A: i64 = 1664525;
const LCG_C: i64 = 1013904223;
const LCG_M: i64 = 4294967296; // 2^32

/// Initialize or get the global random state
fn ensure_initialized() -> i64 {
    let mut state = GLOBAL_RNG_STATE.write().unwrap();
    if state.is_none() {
        // Initialize with time-based seed
        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_micros();
        *state = Some((now % (LCG_M as u128)) as i64);
    }
    state.unwrap()
}

/// Set the random seed
///
/// # Examples
/// - rt_random_seed(42) sets seed to 42
#[no_mangle]
pub extern "C" fn rt_random_seed(seed: i64) {
    let mut state = GLOBAL_RNG_STATE.write().unwrap();
    *state = Some(seed);
}

/// Get the current random state
///
/// Returns the current seed value
#[no_mangle]
pub extern "C" fn rt_random_getstate() -> i64 {
    ensure_initialized()
}

/// Set the random state
///
/// # Examples
/// - rt_random_setstate(saved_state) restores to saved_state
#[no_mangle]
pub extern "C" fn rt_random_setstate(new_state: i64) {
    let mut state = GLOBAL_RNG_STATE.write().unwrap();
    *state = Some(new_state);
}

/// Generate next random i64 value
///
/// Uses Linear Congruential Generator (LCG)
/// Returns value in range [0, 2^32)
#[no_mangle]
pub extern "C" fn rt_random_next() -> i64 {
    let mut state = GLOBAL_RNG_STATE.write().unwrap();
    if state.is_none() {
        // Initialize with time-based seed
        let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_micros();
        *state = Some((now % (LCG_M as u128)) as i64);
    }

    let current = state.unwrap();
    let next = (LCG_A.wrapping_mul(current).wrapping_add(LCG_C)) % LCG_M;
    *state = Some(next);
    next
}

/// Generate random integer in range [min, max] (inclusive)
///
/// # Examples
/// - rt_random_randint(1, 10) returns value from 1 to 10
#[no_mangle]
pub extern "C" fn rt_random_randint(min: i64, max: i64) -> i64 {
    if min > max {
        return min;
    }
    let range = (max - min + 1) as i64;
    let rand_val = rt_random_next();
    min + (rand_val % range)
}

/// Generate random f64 in range [0.0, 1.0)
///
/// # Examples
/// - rt_random_random() returns value from 0.0 to 0.999...
#[no_mangle]
pub extern "C" fn rt_random_random() -> f64 {
    let rand_val = rt_random_next();
    (rand_val as f64) / (LCG_M as f64)
}

/// Generate random f64 in range [min, max)
///
/// # Examples
/// - rt_random_uniform(5.0, 10.0) returns value from 5.0 to 10.0
#[no_mangle]
pub extern "C" fn rt_random_uniform(min: f64, max: f64) -> f64 {
    let r = rt_random_random();
    min + r * (max - min)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_seed_deterministic() {
        rt_random_seed(42);
        let val1 = rt_random_next();
        rt_random_seed(42);
        let val2 = rt_random_next();
        assert_eq!(val1, val2, "Same seed should produce same sequence");
    }

    #[test]
    fn test_randint_range() {
        rt_random_seed(42);
        for _ in 0..100 {
            let val = rt_random_randint(1, 10);
            assert!(val >= 1 && val <= 10, "Value {} out of range [1, 10]", val);
        }
    }

    #[test]
    fn test_random_range() {
        rt_random_seed(42);
        for _ in 0..100 {
            let val = rt_random_random();
            assert!(val >= 0.0 && val < 1.0, "Value {} out of range [0.0, 1.0)", val);
        }
    }

    #[test]
    fn test_uniform_range() {
        rt_random_seed(42);
        for _ in 0..100 {
            let val = rt_random_uniform(5.0, 10.0);
            assert!(val >= 5.0 && val < 10.0, "Value {} out of range [5.0, 10.0)", val);
        }
    }

    #[test]
    fn test_getstate_setstate() {
        rt_random_seed(100);
        let state1 = rt_random_getstate();
        rt_random_next(); // Advance state
        rt_random_setstate(state1); // Restore
        let state2 = rt_random_getstate();
        assert_eq!(state1, state2, "State should be restored");
    }
}
