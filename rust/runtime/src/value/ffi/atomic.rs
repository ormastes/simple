//! Atomic operations FFI functions for Simple runtime.
//!
//! This module provides thread-safe atomic operations:
//! - AtomicBool - Atomic boolean with load, store, swap operations
//! - AtomicInt - Atomic integer with arithmetic and bitwise operations
//! - AtomicFlag - Simple test-and-set flag
//! - Once - One-time initialization primitive

use parking_lot::Mutex;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::Once as StdOnce;

// ============================================================================
// Atomic Storage Maps
// ============================================================================

lazy_static::lazy_static! {
    static ref ATOMIC_BOOL_MAP: Mutex<HashMap<i64, Box<AtomicBool>>> = Mutex::new(HashMap::new());
    static ref ATOMIC_INT_MAP: Mutex<HashMap<i64, Box<AtomicI64>>> = Mutex::new(HashMap::new());
    static ref ATOMIC_FLAG_MAP: Mutex<HashMap<i64, Box<AtomicBool>>> = Mutex::new(HashMap::new());
    static ref ONCE_MAP: Mutex<HashMap<i64, Box<StdOnce>>> = Mutex::new(HashMap::new());
}

static mut ATOMIC_BOOL_COUNTER: i64 = 1;
static mut ATOMIC_INT_COUNTER: i64 = 1;
static mut ATOMIC_FLAG_COUNTER: i64 = 1;
static mut ONCE_COUNTER: i64 = 1;

// ============================================================================
// AtomicBool Operations
// ============================================================================

/// Create a new atomic boolean
#[no_mangle]
pub extern "C" fn rt_atomic_bool_new(initial: bool) -> i64 {
    let atomic = Box::new(AtomicBool::new(initial));
    unsafe {
        let handle = ATOMIC_BOOL_COUNTER;
        ATOMIC_BOOL_COUNTER += 1;
        ATOMIC_BOOL_MAP.lock().insert(handle, atomic);
        handle
    }
}

/// Load value from atomic boolean
#[no_mangle]
pub extern "C" fn rt_atomic_bool_load(handle: i64) -> bool {
    ATOMIC_BOOL_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.load(Ordering::SeqCst))
        .unwrap_or(false)
}

/// Store value to atomic boolean
#[no_mangle]
pub extern "C" fn rt_atomic_bool_store(handle: i64, value: bool) {
    if let Some(atomic) = ATOMIC_BOOL_MAP.lock().get(&handle) {
        atomic.store(value, Ordering::SeqCst);
    }
}

/// Swap value of atomic boolean
#[no_mangle]
pub extern "C" fn rt_atomic_bool_swap(handle: i64, value: bool) -> bool {
    ATOMIC_BOOL_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.swap(value, Ordering::SeqCst))
        .unwrap_or(false)
}

/// Free atomic boolean
#[no_mangle]
pub extern "C" fn rt_atomic_bool_free(handle: i64) {
    ATOMIC_BOOL_MAP.lock().remove(&handle);
}

// ============================================================================
// AtomicInt Operations
// ============================================================================

/// Create a new atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_new(initial: i64) -> i64 {
    let atomic = Box::new(AtomicI64::new(initial));
    unsafe {
        let handle = ATOMIC_INT_COUNTER;
        ATOMIC_INT_COUNTER += 1;
        ATOMIC_INT_MAP.lock().insert(handle, atomic);
        handle
    }
}

/// Load value from atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_load(handle: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.load(Ordering::SeqCst))
        .unwrap_or(0)
}

/// Store value to atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_store(handle: i64, value: i64) {
    if let Some(atomic) = ATOMIC_INT_MAP.lock().get(&handle) {
        atomic.store(value, Ordering::SeqCst);
    }
}

/// Swap value of atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_swap(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.swap(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Compare and exchange atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_compare_exchange(handle: i64, current: i64, new: i64) -> bool {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| {
            atomic
                .compare_exchange(current, new, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
        })
        .unwrap_or(false)
}

/// Fetch and add to atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_fetch_add(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.fetch_add(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Fetch and subtract from atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_fetch_sub(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.fetch_sub(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Fetch and bitwise AND with atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_fetch_and(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.fetch_and(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Fetch and bitwise OR with atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_fetch_or(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.fetch_or(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Fetch and bitwise XOR with atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_fetch_xor(handle: i64, value: i64) -> i64 {
    ATOMIC_INT_MAP
        .lock()
        .get(&handle)
        .map(|atomic| atomic.fetch_xor(value, Ordering::SeqCst))
        .unwrap_or(0)
}

/// Free atomic integer
#[no_mangle]
pub extern "C" fn rt_atomic_int_free(handle: i64) {
    ATOMIC_INT_MAP.lock().remove(&handle);
}

// ============================================================================
// AtomicFlag Operations (simpler bool without load)
// ============================================================================

/// Create a new AtomicFlag (initially false)
#[no_mangle]
pub extern "C" fn rt_atomic_flag_new() -> i64 {
    let flag = Box::new(AtomicBool::new(false));
    unsafe {
        let handle = ATOMIC_FLAG_COUNTER;
        ATOMIC_FLAG_COUNTER += 1;
        ATOMIC_FLAG_MAP.lock().insert(handle, flag);
        handle
    }
}

/// Test and set atomic flag
/// Returns true if flag was already set, false if it was clear
#[no_mangle]
pub extern "C" fn rt_atomic_flag_test_and_set(handle: i64) -> bool {
    ATOMIC_FLAG_MAP
        .lock()
        .get(&handle)
        .map(|flag| flag.swap(true, Ordering::SeqCst))
        .unwrap_or(false)
}

/// Clear atomic flag
#[no_mangle]
pub extern "C" fn rt_atomic_flag_clear(handle: i64) {
    if let Some(flag) = ATOMIC_FLAG_MAP.lock().get(&handle) {
        flag.store(false, Ordering::SeqCst);
    }
}

/// Free atomic flag
#[no_mangle]
pub extern "C" fn rt_atomic_flag_free(handle: i64) {
    ATOMIC_FLAG_MAP.lock().remove(&handle);
}

// ============================================================================
// Once Operations (one-time initialization)
// ============================================================================

/// Create a new Once
#[no_mangle]
pub extern "C" fn rt_once_new() -> i64 {
    let once = Box::new(StdOnce::new());
    unsafe {
        let handle = ONCE_COUNTER;
        ONCE_COUNTER += 1;
        ONCE_MAP.lock().insert(handle, once);
        handle
    }
}

/// Call function once (takes function pointer)
/// Note: In real implementation, this would need FFI callback support
#[no_mangle]
pub extern "C" fn rt_once_call(handle: i64, _func_ptr: i64) {
    // For now, just mark as called
    // Full implementation needs callback infrastructure
    if let Some(_once) = ONCE_MAP.lock().get(&handle) {
        // once.call_once(|| { /* call func_ptr */ });
    }
}

/// Check if Once has been called
#[no_mangle]
pub extern "C" fn rt_once_is_completed(handle: i64) -> bool {
    ONCE_MAP
        .lock()
        .get(&handle)
        .map(|once| once.is_completed())
        .unwrap_or(false)
}

/// Free Once
#[no_mangle]
pub extern "C" fn rt_once_free(handle: i64) {
    ONCE_MAP.lock().remove(&handle);
}

// ============================================================================
// Registry Cleanup (for test isolation)
// ============================================================================

/// Clear all atomic registries (for test cleanup)
pub fn clear_atomic_registries() {
    ATOMIC_BOOL_MAP.lock().clear();
    ATOMIC_INT_MAP.lock().clear();
    ATOMIC_FLAG_MAP.lock().clear();
    ONCE_MAP.lock().clear();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_bool_basic() {
        let handle = rt_atomic_bool_new(false);
        assert_eq!(rt_atomic_bool_load(handle), false);

        rt_atomic_bool_store(handle, true);
        assert_eq!(rt_atomic_bool_load(handle), true);

        rt_atomic_bool_free(handle);
    }

    #[test]
    fn test_atomic_bool_swap() {
        let handle = rt_atomic_bool_new(false);

        let old = rt_atomic_bool_swap(handle, true);
        assert_eq!(old, false);
        assert_eq!(rt_atomic_bool_load(handle), true);

        let old = rt_atomic_bool_swap(handle, false);
        assert_eq!(old, true);
        assert_eq!(rt_atomic_bool_load(handle), false);

        rt_atomic_bool_free(handle);
    }

    #[test]
    fn test_atomic_int_basic() {
        let handle = rt_atomic_int_new(42);
        assert_eq!(rt_atomic_int_load(handle), 42);

        rt_atomic_int_store(handle, 100);
        assert_eq!(rt_atomic_int_load(handle), 100);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_swap() {
        let handle = rt_atomic_int_new(10);

        let old = rt_atomic_int_swap(handle, 20);
        assert_eq!(old, 10);
        assert_eq!(rt_atomic_int_load(handle), 20);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_compare_exchange() {
        let handle = rt_atomic_int_new(100);

        // Successful exchange
        assert!(rt_atomic_int_compare_exchange(handle, 100, 200));
        assert_eq!(rt_atomic_int_load(handle), 200);

        // Failed exchange (current value is 200, not 100)
        assert!(!rt_atomic_int_compare_exchange(handle, 100, 300));
        assert_eq!(rt_atomic_int_load(handle), 200);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_fetch_add() {
        let handle = rt_atomic_int_new(10);

        let old = rt_atomic_int_fetch_add(handle, 5);
        assert_eq!(old, 10);
        assert_eq!(rt_atomic_int_load(handle), 15);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_fetch_sub() {
        let handle = rt_atomic_int_new(20);

        let old = rt_atomic_int_fetch_sub(handle, 7);
        assert_eq!(old, 20);
        assert_eq!(rt_atomic_int_load(handle), 13);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_fetch_and() {
        let handle = rt_atomic_int_new(0b1111);

        let old = rt_atomic_int_fetch_and(handle, 0b1100);
        assert_eq!(old, 0b1111);
        assert_eq!(rt_atomic_int_load(handle), 0b1100);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_fetch_or() {
        let handle = rt_atomic_int_new(0b1010);

        let old = rt_atomic_int_fetch_or(handle, 0b0101);
        assert_eq!(old, 0b1010);
        assert_eq!(rt_atomic_int_load(handle), 0b1111);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_int_fetch_xor() {
        let handle = rt_atomic_int_new(0b1010);

        let old = rt_atomic_int_fetch_xor(handle, 0b1100);
        assert_eq!(old, 0b1010);
        assert_eq!(rt_atomic_int_load(handle), 0b0110);

        rt_atomic_int_free(handle);
    }

    #[test]
    fn test_atomic_flag() {
        let handle = rt_atomic_flag_new();

        // First test_and_set should return false (was clear)
        assert_eq!(rt_atomic_flag_test_and_set(handle), false);

        // Second test_and_set should return true (was set)
        assert_eq!(rt_atomic_flag_test_and_set(handle), true);

        // Clear the flag
        rt_atomic_flag_clear(handle);

        // After clear, test_and_set should return false again
        assert_eq!(rt_atomic_flag_test_and_set(handle), false);

        rt_atomic_flag_free(handle);
    }

    #[test]
    fn test_once() {
        let handle = rt_once_new();

        // Initially not completed
        assert_eq!(rt_once_is_completed(handle), false);

        // Call once (stub implementation doesn't actually call)
        rt_once_call(handle, 0);

        // Note: Since rt_once_call is a stub, is_completed won't change
        // In a full implementation, this would be true after calling

        rt_once_free(handle);
    }

    #[test]
    fn test_atomic_bool_invalid_handle() {
        // Operations on invalid handle should not panic
        assert_eq!(rt_atomic_bool_load(99999), false);
        rt_atomic_bool_store(99999, true);
        assert_eq!(rt_atomic_bool_swap(99999, true), false);
        rt_atomic_bool_free(99999);
    }

    #[test]
    fn test_atomic_int_invalid_handle() {
        // Operations on invalid handle should not panic
        assert_eq!(rt_atomic_int_load(99999), 0);
        rt_atomic_int_store(99999, 42);
        assert_eq!(rt_atomic_int_swap(99999, 42), 0);
        assert_eq!(rt_atomic_int_compare_exchange(99999, 0, 1), false);
        assert_eq!(rt_atomic_int_fetch_add(99999, 1), 0);
        rt_atomic_int_free(99999);
    }

    #[test]
    fn test_multiple_atomics() {
        // Create multiple atomic bools
        let h1 = rt_atomic_bool_new(false);
        let h2 = rt_atomic_bool_new(true);
        let h3 = rt_atomic_bool_new(false);

        assert_eq!(rt_atomic_bool_load(h1), false);
        assert_eq!(rt_atomic_bool_load(h2), true);
        assert_eq!(rt_atomic_bool_load(h3), false);

        rt_atomic_bool_free(h1);
        rt_atomic_bool_free(h2);
        rt_atomic_bool_free(h3);

        // Create multiple atomic ints
        let i1 = rt_atomic_int_new(10);
        let i2 = rt_atomic_int_new(20);

        assert_eq!(rt_atomic_int_load(i1), 10);
        assert_eq!(rt_atomic_int_load(i2), 20);

        rt_atomic_int_free(i1);
        rt_atomic_int_free(i2);
    }
}
