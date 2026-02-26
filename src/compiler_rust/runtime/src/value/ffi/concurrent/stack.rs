//! Concurrent stack FFI.
//!
//! Provides a thread-safe LIFO stack for work-stealing or backtracking algorithms.
//! Uses Vec internally with Mutex synchronization.

use crate::value::core::RuntimeValue;
use std::collections::HashMap;
use std::sync::Mutex;

struct ConcurrentStack {
    data: Mutex<Vec<RuntimeValue>>,
}

impl ConcurrentStack {
    fn new() -> Self {
        Self {
            data: Mutex::new(Vec::new()),
        }
    }
}

lazy_static::lazy_static! {
    static ref CONCURRENT_STACK_MAP: Mutex<HashMap<i64, Box<ConcurrentStack>>> = Mutex::new(HashMap::new());
}

static mut CONCURRENT_STACK_COUNTER: i64 = 1;

/// Create a new concurrent stack
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_new() -> i64 {
    let stack = Box::new(ConcurrentStack::new());
    unsafe {
        let handle = CONCURRENT_STACK_COUNTER;
        CONCURRENT_STACK_COUNTER += 1;
        CONCURRENT_STACK_MAP.lock().unwrap().insert(handle, stack);
        handle
    }
}

/// Push value to concurrent stack
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_push(handle: i64, value: RuntimeValue) {
    if let Some(stack) = CONCURRENT_STACK_MAP.lock().unwrap().get(&handle) {
        stack.data.lock().unwrap().push(value);
    }
}

/// Pop value from concurrent stack
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_pop(handle: i64) -> RuntimeValue {
    CONCURRENT_STACK_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|stack| stack.data.lock().unwrap().pop())
        .unwrap_or(RuntimeValue::NIL)
}

/// Check if concurrent stack is empty
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_is_empty(handle: i64) -> bool {
    CONCURRENT_STACK_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|stack| stack.data.lock().unwrap().is_empty())
        .unwrap_or(true)
}

/// Get concurrent stack length
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_len(handle: i64) -> i64 {
    CONCURRENT_STACK_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|stack| stack.data.lock().unwrap().len() as i64)
        .unwrap_or(0)
}

/// Free concurrent stack
#[no_mangle]
pub extern "C" fn rt_concurrent_stack_free(handle: i64) {
    CONCURRENT_STACK_MAP.lock().unwrap().remove(&handle);
}

/// Clear all concurrent stack handles (for test cleanup)
pub fn clear_concurrent_stack_registry() {
    CONCURRENT_STACK_MAP.lock().unwrap().clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concurrent_stack_new() {
        let handle = rt_concurrent_stack_new();
        assert!(handle > 0);
        assert!(rt_concurrent_stack_is_empty(handle));
        assert_eq!(rt_concurrent_stack_len(handle), 0);
        rt_concurrent_stack_free(handle);
    }

    #[test]
    fn test_concurrent_stack_push_pop() {
        let handle = rt_concurrent_stack_new();

        rt_concurrent_stack_push(handle, RuntimeValue::from_int(1));
        rt_concurrent_stack_push(handle, RuntimeValue::from_int(2));
        rt_concurrent_stack_push(handle, RuntimeValue::from_int(3));

        assert_eq!(rt_concurrent_stack_len(handle), 3);
        assert!(!rt_concurrent_stack_is_empty(handle));

        // LIFO order
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 3);
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 2);
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 1);

        assert!(rt_concurrent_stack_is_empty(handle));
        rt_concurrent_stack_free(handle);
    }

    #[test]
    fn test_concurrent_stack_pop_empty() {
        let handle = rt_concurrent_stack_new();

        let val = rt_concurrent_stack_pop(handle);
        assert!(val.is_nil());

        rt_concurrent_stack_free(handle);
    }

    #[test]
    fn test_concurrent_stack_lifo_order() {
        let handle = rt_concurrent_stack_new();

        for i in 0..100 {
            rt_concurrent_stack_push(handle, RuntimeValue::from_int(i));
        }

        // Pop in reverse order (LIFO)
        for i in (0..100).rev() {
            assert_eq!(rt_concurrent_stack_pop(handle).as_int(), i);
        }

        assert!(rt_concurrent_stack_is_empty(handle));
        rt_concurrent_stack_free(handle);
    }

    #[test]
    fn test_concurrent_stack_interleaved() {
        let handle = rt_concurrent_stack_new();

        rt_concurrent_stack_push(handle, RuntimeValue::from_int(1));
        rt_concurrent_stack_push(handle, RuntimeValue::from_int(2));
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 2); // Last in

        rt_concurrent_stack_push(handle, RuntimeValue::from_int(3));
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 3);
        assert_eq!(rt_concurrent_stack_pop(handle).as_int(), 1); // First in

        assert!(rt_concurrent_stack_is_empty(handle));
        rt_concurrent_stack_free(handle);
    }

    #[test]
    fn test_concurrent_stack_invalid_handle() {
        rt_concurrent_stack_push(999999, RuntimeValue::from_int(42)); // Should not crash
        assert!(rt_concurrent_stack_pop(999999).is_nil());
        assert!(rt_concurrent_stack_is_empty(999999));
        assert_eq!(rt_concurrent_stack_len(999999), 0);
        rt_concurrent_stack_free(999999); // Should not crash
    }

    #[test]
    fn test_concurrent_stack_double_free() {
        let handle = rt_concurrent_stack_new();
        rt_concurrent_stack_free(handle);
        rt_concurrent_stack_free(handle); // Should be safe
    }
}
