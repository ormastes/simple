//! Synchronization primitives FFI functions for Simple runtime.
//!
//! This module provides thread synchronization and coordination primitives:
//! - Condition Variables (Condvar) - Wait and signal synchronization
//! - RwLock helpers - Read/write lock utilities
//! - Thread-Local Storage - Alternative RuntimeValue-based TLS API
//! - Threading utilities - CPU hints and optimizations

use crate::value::RuntimeValue;
use parking_lot::Mutex;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Condvar as StdCondvar;

// ============================================================================
// Condvar Operations (Condition Variables)
// ============================================================================

lazy_static::lazy_static! {
    static ref CONDVAR_MAP: Mutex<HashMap<i64, Box<StdCondvar>>> = Mutex::new(HashMap::new());
}

static mut CONDVAR_COUNTER: i64 = 1;

/// Create a new condition variable
#[no_mangle]
pub extern "C" fn rt_condvar_new() -> i64 {
    let condvar = Box::new(StdCondvar::new());
    unsafe {
        let handle = CONDVAR_COUNTER;
        CONDVAR_COUNTER += 1;
        CONDVAR_MAP.lock().insert(handle, condvar);
        handle
    }
}

/// Wait on condvar (note: simplified, real impl needs mutex integration)
/// This is a stub implementation - full version requires mutex guard integration
#[no_mangle]
pub extern "C" fn rt_condvar_wait(handle: i64, _mutex_handle: i64) {
    // Simplified stub - full implementation needs proper mutex integration
    if let Some(_condvar) = CONDVAR_MAP.lock().get(&handle) {
        // condvar.wait(mutex_guard);
    }
}

/// Wait on condvar with timeout (milliseconds)
/// Returns 1 if notified, 0 if timeout, -1 on error
#[no_mangle]
pub extern "C" fn rt_condvar_wait_timeout(condvar_handle: i64, _mutex_handle: i64, timeout_ms: u64) -> i64 {
    // Simplified implementation - real version needs proper mutex integration
    if CONDVAR_MAP.lock().get(&condvar_handle).is_some() {
        // In a real implementation, we'd wait with timeout on the condvar
        // For now, just sleep for the timeout period and return timeout
        std::thread::sleep(std::time::Duration::from_millis(timeout_ms));
        0 // timeout
    } else {
        -1 // error: invalid handle
    }
}

/// Notify one waiting thread
#[no_mangle]
pub extern "C" fn rt_condvar_notify_one(handle: i64) {
    if let Some(condvar) = CONDVAR_MAP.lock().get(&handle) {
        condvar.notify_one();
    }
}

/// Notify all waiting threads
#[no_mangle]
pub extern "C" fn rt_condvar_notify_all(handle: i64) {
    if let Some(condvar) = CONDVAR_MAP.lock().get(&handle) {
        condvar.notify_all();
    }
}

/// Free condition variable
#[no_mangle]
pub extern "C" fn rt_condvar_free(handle: i64) {
    CONDVAR_MAP.lock().remove(&handle);
}

// ============================================================================
// Threading Utilities
// ============================================================================

/// Hint to CPU for spin loops
/// Improves performance and power efficiency in spin-wait scenarios
#[no_mangle]
pub extern "C" fn rt_spin_loop_hint() {
    std::hint::spin_loop();
}

// ============================================================================
// RwLock Extended (No-op unlock functions)
// ============================================================================

/// Unlock read lock (no-op in Rust, handled by RAII)
/// Provided for API compatibility with languages that require explicit unlock
#[no_mangle]
pub extern "C" fn rt_rwlock_unlock_read(_handle: i64) {
    // No-op: locks are released automatically when guard is dropped
}

/// Unlock write lock (no-op in Rust, handled by RAII)
/// Provided for API compatibility with languages that require explicit unlock
#[no_mangle]
pub extern "C" fn rt_rwlock_unlock_write(_handle: i64) {
    // No-op: locks are released automatically when guard is dropped
}

// ============================================================================
// Thread-Local Storage (Alternative API)
// ============================================================================
// This is an alternative TLS API that stores RuntimeValue directly
// See ffi/concurrent/tls.rs for the u64-based TLS API

thread_local! {
    static THREAD_LOCAL_STORAGE: RefCell<HashMap<i64, RuntimeValue>> = RefCell::new(HashMap::new());
}

lazy_static::lazy_static! {
    static ref THREAD_LOCAL_HANDLES: Mutex<HashSet<i64>> = Mutex::new(HashSet::new());
}

static mut THREAD_LOCAL_COUNTER: i64 = 1;

/// Create new thread-local storage slot
#[no_mangle]
pub extern "C" fn rt_thread_local_new() -> i64 {
    unsafe {
        let handle = THREAD_LOCAL_COUNTER;
        THREAD_LOCAL_COUNTER += 1;
        THREAD_LOCAL_HANDLES.lock().insert(handle);
        handle
    }
}

/// Get value from thread-local storage
/// Returns NIL if handle is invalid or value not set
#[no_mangle]
pub extern "C" fn rt_thread_local_get(handle: i64) -> RuntimeValue {
    // Check if handle is valid
    if !THREAD_LOCAL_HANDLES.lock().contains(&handle) {
        return RuntimeValue::NIL;
    }

    THREAD_LOCAL_STORAGE.with(|storage| storage.borrow().get(&handle).copied().unwrap_or(RuntimeValue::NIL))
}

/// Set value in thread-local storage
#[no_mangle]
pub extern "C" fn rt_thread_local_set(handle: i64, value: RuntimeValue) {
    // Check if handle is valid
    if !THREAD_LOCAL_HANDLES.lock().contains(&handle) {
        return;
    }

    THREAD_LOCAL_STORAGE.with(|storage| {
        storage.borrow_mut().insert(handle, value);
    });
}

/// Free thread-local storage slot
#[no_mangle]
pub extern "C" fn rt_thread_local_free(handle: i64) {
    THREAD_LOCAL_HANDLES.lock().remove(&handle);
    // Note: Each thread's local copy will be cleaned up when thread exits
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_condvar_basic() {
        let handle = rt_condvar_new();
        assert!(handle > 0);

        // Test notify operations don't panic
        rt_condvar_notify_one(handle);
        rt_condvar_notify_all(handle);

        rt_condvar_free(handle);
    }

    #[test]
    fn test_condvar_wait() {
        let handle = rt_condvar_new();

        // Wait is a stub, should not panic
        rt_condvar_wait(handle, 0);

        rt_condvar_free(handle);
    }

    #[test]
    fn test_condvar_wait_timeout() {
        let handle = rt_condvar_new();

        // Should timeout (return 0)
        let result = rt_condvar_wait_timeout(handle, 0, 1);
        assert_eq!(result, 0);

        rt_condvar_free(handle);
    }

    #[test]
    fn test_condvar_invalid_handle() {
        // Operations on invalid handle should not panic
        rt_condvar_notify_one(99999);
        rt_condvar_notify_all(99999);
        rt_condvar_wait(99999, 0);

        let result = rt_condvar_wait_timeout(99999, 0, 1);
        assert_eq!(result, -1); // Error
    }

    #[test]
    fn test_multiple_condvars() {
        let h1 = rt_condvar_new();
        let h2 = rt_condvar_new();
        let h3 = rt_condvar_new();

        assert!(h1 > 0);
        assert!(h2 > 0);
        assert!(h3 > 0);
        assert_ne!(h1, h2);
        assert_ne!(h2, h3);

        rt_condvar_free(h1);
        rt_condvar_free(h2);
        rt_condvar_free(h3);
    }

    #[test]
    fn test_spin_loop_hint() {
        // Should not panic
        rt_spin_loop_hint();
        rt_spin_loop_hint();
    }

    #[test]
    fn test_rwlock_unlock() {
        // No-op functions should not panic
        rt_rwlock_unlock_read(1);
        rt_rwlock_unlock_write(2);
        rt_rwlock_unlock_read(99999);
        rt_rwlock_unlock_write(99999);
    }

    #[test]
    fn test_thread_local_basic() {
        let handle = rt_thread_local_new();
        assert!(handle > 0);

        // Initially should return NIL
        let value = rt_thread_local_get(handle);
        assert!(value.is_nil());

        // Set a value
        let test_val = RuntimeValue::from_int(42);
        rt_thread_local_set(handle, test_val);

        // Get should return the value
        let retrieved = rt_thread_local_get(handle);
        assert!(retrieved.is_int());
        assert_eq!(retrieved.as_int(), 42);

        rt_thread_local_free(handle);
    }

    #[test]
    fn test_thread_local_invalid_handle() {
        // Operations on invalid handle should not panic
        let value = rt_thread_local_get(99999);
        assert!(value.is_nil());

        rt_thread_local_set(99999, RuntimeValue::from_int(123));
        rt_thread_local_free(99999);
    }

    #[test]
    fn test_thread_local_multiple_slots() {
        let h1 = rt_thread_local_new();
        let h2 = rt_thread_local_new();

        assert!(h1 > 0);
        assert!(h2 > 0);
        assert_ne!(h1, h2);

        rt_thread_local_set(h1, RuntimeValue::from_int(10));
        rt_thread_local_set(h2, RuntimeValue::from_int(20));

        assert_eq!(rt_thread_local_get(h1).as_int(), 10);
        assert_eq!(rt_thread_local_get(h2).as_int(), 20);

        rt_thread_local_free(h1);
        rt_thread_local_free(h2);
    }

    #[test]
    fn test_thread_local_update() {
        let handle = rt_thread_local_new();

        rt_thread_local_set(handle, RuntimeValue::from_int(1));
        assert_eq!(rt_thread_local_get(handle).as_int(), 1);

        rt_thread_local_set(handle, RuntimeValue::from_int(2));
        assert_eq!(rt_thread_local_get(handle).as_int(), 2);

        rt_thread_local_set(handle, RuntimeValue::from_int(3));
        assert_eq!(rt_thread_local_get(handle).as_int(), 3);

        rt_thread_local_free(handle);
    }

    #[test]
    fn test_thread_local_isolation() {
        use std::thread;

        let handle = rt_thread_local_new();

        // Set value in main thread
        rt_thread_local_set(handle, RuntimeValue::from_int(100));

        // Spawn thread and check it sees NIL (thread-local)
        let handle_copy = handle;
        let thread_handle = thread::spawn(move || {
            let value = rt_thread_local_get(handle_copy);
            assert!(value.is_nil()); // Should be NIL in new thread

            // Set value in spawned thread
            rt_thread_local_set(handle_copy, RuntimeValue::from_int(200));
            let value2 = rt_thread_local_get(handle_copy);
            assert_eq!(value2.as_int(), 200);
        });

        thread_handle.join().unwrap();

        // Main thread should still see original value
        let value = rt_thread_local_get(handle);
        assert_eq!(value.as_int(), 100);

        rt_thread_local_free(handle);
    }
}
