//! Concurrent queue FFI.
//!
//! Provides a thread-safe FIFO queue for producer-consumer patterns.
//! Uses VecDeque internally with Mutex synchronization.

use crate::value::core::RuntimeValue;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Mutex;

struct ConcurrentQueue {
    data: Mutex<VecDeque<RuntimeValue>>,
}

impl ConcurrentQueue {
    fn new() -> Self {
        Self {
            data: Mutex::new(VecDeque::new()),
        }
    }
}

lazy_static::lazy_static! {
    static ref CONCURRENT_QUEUE_MAP: Mutex<HashMap<i64, Box<ConcurrentQueue>>> = Mutex::new(HashMap::new());
}

static mut CONCURRENT_QUEUE_COUNTER: i64 = 1;

/// Create a new concurrent queue
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_new() -> i64 {
    let queue = Box::new(ConcurrentQueue::new());
    unsafe {
        let handle = CONCURRENT_QUEUE_COUNTER;
        CONCURRENT_QUEUE_COUNTER += 1;
        CONCURRENT_QUEUE_MAP.lock().unwrap().insert(handle, queue);
        handle
    }
}

/// Push value to back of concurrent queue
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_push(handle: i64, value: RuntimeValue) {
    if let Some(queue) = CONCURRENT_QUEUE_MAP.lock().unwrap().get(&handle) {
        queue.data.lock().unwrap().push_back(value);
    }
}

/// Pop value from front of concurrent queue
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_pop(handle: i64) -> RuntimeValue {
    CONCURRENT_QUEUE_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|queue| queue.data.lock().unwrap().pop_front())
        .unwrap_or(RuntimeValue::NIL)
}

/// Check if concurrent queue is empty
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_is_empty(handle: i64) -> bool {
    CONCURRENT_QUEUE_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|queue| queue.data.lock().unwrap().is_empty())
        .unwrap_or(true)
}

/// Get concurrent queue length
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_len(handle: i64) -> i64 {
    CONCURRENT_QUEUE_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|queue| queue.data.lock().unwrap().len() as i64)
        .unwrap_or(0)
}

/// Free concurrent queue
#[no_mangle]
pub extern "C" fn rt_concurrent_queue_free(handle: i64) {
    CONCURRENT_QUEUE_MAP.lock().unwrap().remove(&handle);
}

/// Clear all concurrent queue handles (for test cleanup)
pub fn clear_concurrent_queue_registry() {
    CONCURRENT_QUEUE_MAP.lock().unwrap().clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_concurrent_queue_new() {
        let handle = rt_concurrent_queue_new();
        assert!(handle > 0);
        assert!(rt_concurrent_queue_is_empty(handle));
        assert_eq!(rt_concurrent_queue_len(handle), 0);
        rt_concurrent_queue_free(handle);
    }

    #[test]
    fn test_concurrent_queue_push_pop() {
        let handle = rt_concurrent_queue_new();

        rt_concurrent_queue_push(handle, RuntimeValue::from_int(1));
        rt_concurrent_queue_push(handle, RuntimeValue::from_int(2));
        rt_concurrent_queue_push(handle, RuntimeValue::from_int(3));

        assert_eq!(rt_concurrent_queue_len(handle), 3);
        assert!(!rt_concurrent_queue_is_empty(handle));

        // FIFO order
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 1);
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 2);
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 3);

        assert!(rt_concurrent_queue_is_empty(handle));
        rt_concurrent_queue_free(handle);
    }

    #[test]
    fn test_concurrent_queue_pop_empty() {
        let handle = rt_concurrent_queue_new();

        let val = rt_concurrent_queue_pop(handle);
        assert!(val.is_nil());

        rt_concurrent_queue_free(handle);
    }

    #[test]
    fn test_concurrent_queue_fifo_order() {
        let handle = rt_concurrent_queue_new();

        for i in 0..100 {
            rt_concurrent_queue_push(handle, RuntimeValue::from_int(i));
        }

        for i in 0..100 {
            assert_eq!(rt_concurrent_queue_pop(handle).as_int(), i);
        }

        assert!(rt_concurrent_queue_is_empty(handle));
        rt_concurrent_queue_free(handle);
    }

    #[test]
    fn test_concurrent_queue_interleaved() {
        let handle = rt_concurrent_queue_new();

        rt_concurrent_queue_push(handle, RuntimeValue::from_int(1));
        rt_concurrent_queue_push(handle, RuntimeValue::from_int(2));
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 1);

        rt_concurrent_queue_push(handle, RuntimeValue::from_int(3));
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 2);
        assert_eq!(rt_concurrent_queue_pop(handle).as_int(), 3);

        assert!(rt_concurrent_queue_is_empty(handle));
        rt_concurrent_queue_free(handle);
    }

    #[test]
    fn test_concurrent_queue_invalid_handle() {
        rt_concurrent_queue_push(999999, RuntimeValue::from_int(42)); // Should not crash
        assert!(rt_concurrent_queue_pop(999999).is_nil());
        assert!(rt_concurrent_queue_is_empty(999999));
        assert_eq!(rt_concurrent_queue_len(999999), 0);
        rt_concurrent_queue_free(999999); // Should not crash
    }

    #[test]
    fn test_concurrent_queue_double_free() {
        let handle = rt_concurrent_queue_new();
        rt_concurrent_queue_free(handle);
        rt_concurrent_queue_free(handle); // Should be safe
    }
}
