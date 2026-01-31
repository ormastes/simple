//! Thread-local storage FFI.
//!
//! Provides thread-safe key-value storage with u64 keys.
//! Uses BTreeMap for ordered keys and Mutex for thread safety.

use crate::value::core::RuntimeValue;
use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

struct ThreadLocalStorage {
    data: Mutex<BTreeMap<u64, RuntimeValue>>,
}

impl ThreadLocalStorage {
    fn new() -> Self {
        Self {
            data: Mutex::new(BTreeMap::new()),
        }
    }
}

lazy_static::lazy_static! {
    static ref TLS_MAP: Mutex<HashMap<i64, Box<ThreadLocalStorage>>> = Mutex::new(HashMap::new());
}

static mut TLS_COUNTER: i64 = 1;

/// Create a new thread-local storage
#[no_mangle]
pub extern "C" fn rt_tls_new() -> i64 {
    let tls = Box::new(ThreadLocalStorage::new());
    unsafe {
        let handle = TLS_COUNTER;
        TLS_COUNTER += 1;
        TLS_MAP.lock().unwrap().insert(handle, tls);
        handle
    }
}

/// Set thread-local value
#[no_mangle]
pub extern "C" fn rt_tls_set(handle: i64, key: u64, value: RuntimeValue) {
    if let Some(tls) = TLS_MAP.lock().unwrap().get(&handle) {
        tls.data.lock().unwrap().insert(key, value);
    }
}

/// Get thread-local value
#[no_mangle]
pub extern "C" fn rt_tls_get(handle: i64, key: u64) -> RuntimeValue {
    TLS_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|tls| tls.data.lock().unwrap().get(&key).copied())
        .unwrap_or(RuntimeValue::NIL)
}

/// Remove thread-local value
#[no_mangle]
pub extern "C" fn rt_tls_remove(handle: i64, key: u64) -> RuntimeValue {
    TLS_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|tls| tls.data.lock().unwrap().remove(&key))
        .unwrap_or(RuntimeValue::NIL)
}

/// Clear all thread-local values
#[no_mangle]
pub extern "C" fn rt_tls_clear(handle: i64) {
    if let Some(tls) = TLS_MAP.lock().unwrap().get(&handle) {
        tls.data.lock().unwrap().clear();
    }
}

/// Free thread-local storage
#[no_mangle]
pub extern "C" fn rt_tls_free(handle: i64) {
    TLS_MAP.lock().unwrap().remove(&handle);
}

/// Clear all TLS handles (for test cleanup)
pub fn clear_tls_registry() {
    TLS_MAP.lock().unwrap().clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tls_new() {
        let handle = rt_tls_new();
        assert!(handle > 0);
        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_set_and_get() {
        let handle = rt_tls_new();

        rt_tls_set(handle, 1, RuntimeValue::from_int(42));
        rt_tls_set(handle, 2, RuntimeValue::from_int(99));

        assert_eq!(rt_tls_get(handle, 1).as_int(), 42);
        assert_eq!(rt_tls_get(handle, 2).as_int(), 99);

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_get_nonexistent() {
        let handle = rt_tls_new();

        let val = rt_tls_get(handle, 999);
        assert!(val.is_nil());

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_remove() {
        let handle = rt_tls_new();

        rt_tls_set(handle, 1, RuntimeValue::from_int(42));

        let removed = rt_tls_remove(handle, 1);
        assert_eq!(removed.as_int(), 42);

        // Getting again returns NIL
        let val = rt_tls_get(handle, 1);
        assert!(val.is_nil());

        // Removing again returns NIL
        let removed2 = rt_tls_remove(handle, 1);
        assert!(removed2.is_nil());

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_clear() {
        let handle = rt_tls_new();

        for i in 0..10 {
            rt_tls_set(handle, i, RuntimeValue::from_int(i as i64 * 10));
        }

        rt_tls_clear(handle);

        // All values should be gone
        for i in 0..10 {
            assert!(rt_tls_get(handle, i).is_nil());
        }

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_overwrite() {
        let handle = rt_tls_new();

        rt_tls_set(handle, 1, RuntimeValue::from_int(42));
        rt_tls_set(handle, 1, RuntimeValue::from_int(99));

        assert_eq!(rt_tls_get(handle, 1).as_int(), 99);

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_multiple_keys() {
        let handle = rt_tls_new();

        for i in 0..100 {
            rt_tls_set(handle, i, RuntimeValue::from_int(i as i64));
        }

        for i in 0..100 {
            assert_eq!(rt_tls_get(handle, i).as_int(), i as i64);
        }

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_large_keys() {
        let handle = rt_tls_new();

        let large_key = u64::MAX - 1;
        rt_tls_set(handle, large_key, RuntimeValue::from_int(42));

        assert_eq!(rt_tls_get(handle, large_key).as_int(), 42);

        rt_tls_free(handle);
    }

    #[test]
    fn test_tls_invalid_handle() {
        rt_tls_set(999999, 1, RuntimeValue::from_int(42)); // Should not crash
        assert!(rt_tls_get(999999, 1).is_nil());
        assert!(rt_tls_remove(999999, 1).is_nil());
        rt_tls_clear(999999); // Should not crash
        rt_tls_free(999999); // Should not crash
    }

    #[test]
    fn test_tls_double_free() {
        let handle = rt_tls_new();
        rt_tls_free(handle);
        rt_tls_free(handle); // Should be safe
    }
}
