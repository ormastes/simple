//! Concurrent map FFI.
//!
//! Provides a thread-safe key-value map for sharing data between threads.
//! Uses Mutex for synchronization, suitable for moderate contention scenarios.

use crate::value::core::RuntimeValue;
use std::collections::HashMap;
use std::sync::Mutex;

struct ConcurrentMap {
    data: Mutex<HashMap<i64, RuntimeValue>>,
}

impl ConcurrentMap {
    fn new() -> Self {
        Self {
            data: Mutex::new(HashMap::new()),
        }
    }
}

lazy_static::lazy_static! {
    static ref CONCURRENT_MAP_MAP: Mutex<HashMap<i64, Box<ConcurrentMap>>> = Mutex::new(HashMap::new());
}

static mut CONCURRENT_MAP_COUNTER: i64 = 1;

/// Create a new concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_new() -> i64 {
    let map = Box::new(ConcurrentMap::new());
    unsafe {
        let handle = CONCURRENT_MAP_COUNTER;
        CONCURRENT_MAP_COUNTER += 1;
        CONCURRENT_MAP_MAP.lock().unwrap().insert(handle, map);
        handle
    }
}

/// Insert key-value pair into concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_insert(handle: i64, key: i64, value: RuntimeValue) {
    if let Some(map) = CONCURRENT_MAP_MAP.lock().unwrap().get(&handle) {
        map.data.lock().unwrap().insert(key, value);
    }
}

/// Get value from concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_get(handle: i64, key: i64) -> RuntimeValue {
    CONCURRENT_MAP_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.data.lock().unwrap().get(&key).copied())
        .unwrap_or(RuntimeValue::NIL)
}

/// Remove key from concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_remove(handle: i64, key: i64) -> RuntimeValue {
    CONCURRENT_MAP_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|map| map.data.lock().unwrap().remove(&key))
        .unwrap_or(RuntimeValue::NIL)
}

/// Check if concurrent map contains key
#[no_mangle]
pub extern "C" fn rt_concurrent_map_contains(handle: i64, key: i64) -> bool {
    CONCURRENT_MAP_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.data.lock().unwrap().contains_key(&key))
        .unwrap_or(false)
}

/// Get concurrent map length
#[no_mangle]
pub extern "C" fn rt_concurrent_map_len(handle: i64) -> i64 {
    CONCURRENT_MAP_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|map| map.data.lock().unwrap().len() as i64)
        .unwrap_or(0)
}

/// Clear concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_clear(handle: i64) {
    if let Some(map) = CONCURRENT_MAP_MAP.lock().unwrap().get(&handle) {
        map.data.lock().unwrap().clear();
    }
}

/// Free concurrent map
#[no_mangle]
pub extern "C" fn rt_concurrent_map_free(handle: i64) {
    CONCURRENT_MAP_MAP.lock().unwrap().remove(&handle);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concurrent_map_new() {
        let handle = rt_concurrent_map_new();
        assert!(handle > 0);
        assert_eq!(rt_concurrent_map_len(handle), 0);
        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_insert_and_get() {
        let handle = rt_concurrent_map_new();

        let val1 = RuntimeValue::from_int(42);
        let val2 = RuntimeValue::from_int(99);

        rt_concurrent_map_insert(handle, 1, val1);
        rt_concurrent_map_insert(handle, 2, val2);

        assert_eq!(rt_concurrent_map_get(handle, 1).as_int(), 42);
        assert_eq!(rt_concurrent_map_get(handle, 2).as_int(), 99);
        assert_eq!(rt_concurrent_map_len(handle), 2);

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_get_nonexistent() {
        let handle = rt_concurrent_map_new();

        let val = rt_concurrent_map_get(handle, 999);
        assert!(val.is_nil());

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_contains() {
        let handle = rt_concurrent_map_new();

        let val = RuntimeValue::from_int(42);
        rt_concurrent_map_insert(handle, 1, val);

        assert!(rt_concurrent_map_contains(handle, 1));
        assert!(!rt_concurrent_map_contains(handle, 2));

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_remove() {
        let handle = rt_concurrent_map_new();

        let val = RuntimeValue::from_int(42);
        rt_concurrent_map_insert(handle, 1, val);

        assert_eq!(rt_concurrent_map_len(handle), 1);

        let removed = rt_concurrent_map_remove(handle, 1);
        assert_eq!(removed.as_int(), 42);
        assert_eq!(rt_concurrent_map_len(handle), 0);

        // Removing again returns NIL
        let removed2 = rt_concurrent_map_remove(handle, 1);
        assert!(removed2.is_nil());

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_clear() {
        let handle = rt_concurrent_map_new();

        for i in 0..10 {
            rt_concurrent_map_insert(handle, i, RuntimeValue::from_int(i * 10));
        }

        assert_eq!(rt_concurrent_map_len(handle), 10);

        rt_concurrent_map_clear(handle);
        assert_eq!(rt_concurrent_map_len(handle), 0);

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_overwrite() {
        let handle = rt_concurrent_map_new();

        rt_concurrent_map_insert(handle, 1, RuntimeValue::from_int(42));
        rt_concurrent_map_insert(handle, 1, RuntimeValue::from_int(99));

        assert_eq!(rt_concurrent_map_get(handle, 1).as_int(), 99);
        assert_eq!(rt_concurrent_map_len(handle), 1); // Still one entry

        rt_concurrent_map_free(handle);
    }

    #[test]
    fn test_concurrent_map_invalid_handle() {
        rt_concurrent_map_insert(999999, 1, RuntimeValue::from_int(42)); // Should not crash
        assert!(rt_concurrent_map_get(999999, 1).is_nil());
        assert!(!rt_concurrent_map_contains(999999, 1));
        assert_eq!(rt_concurrent_map_len(999999), 0);
        rt_concurrent_map_clear(999999); // Should not crash
        rt_concurrent_map_free(999999); // Should not crash
    }

    #[test]
    fn test_concurrent_map_double_free() {
        let handle = rt_concurrent_map_new();
        rt_concurrent_map_free(handle);
        rt_concurrent_map_free(handle); // Should be safe
    }
}
