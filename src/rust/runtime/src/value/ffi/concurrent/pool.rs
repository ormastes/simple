//! Resource pool FFI.
//!
//! Provides a bounded pool for reusing expensive resources (connections, buffers, etc.).
//! Useful for connection pooling, object pooling, and memory recycling.

use crate::value::core::RuntimeValue;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::sync::Mutex;

struct ResourcePool {
    available: Mutex<VecDeque<RuntimeValue>>,
    capacity: usize,
}

impl ResourcePool {
    fn new(capacity: usize) -> Self {
        Self {
            available: Mutex::new(VecDeque::new()),
            capacity,
        }
    }
}

lazy_static::lazy_static! {
    static ref POOL_MAP: Mutex<HashMap<i64, Box<ResourcePool>>> = Mutex::new(HashMap::new());
}

static mut POOL_COUNTER: i64 = 1;

/// Create a new resource pool with given capacity
#[no_mangle]
pub extern "C" fn rt_pool_new(capacity: i64) -> i64 {
    let pool = Box::new(ResourcePool::new(capacity as usize));
    unsafe {
        let handle = POOL_COUNTER;
        POOL_COUNTER += 1;
        POOL_MAP.lock().unwrap().insert(handle, pool);
        handle
    }
}

/// Acquire a resource from the pool
/// Returns NIL if pool is empty
#[no_mangle]
pub extern "C" fn rt_pool_acquire(handle: i64) -> RuntimeValue {
    POOL_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .and_then(|pool| pool.available.lock().unwrap().pop_front())
        .unwrap_or(RuntimeValue::NIL)
}

/// Release a resource back to the pool
#[no_mangle]
pub extern "C" fn rt_pool_release(handle: i64, resource: RuntimeValue) {
    if let Some(pool) = POOL_MAP.lock().unwrap().get(&handle) {
        let mut available = pool.available.lock().unwrap();
        if available.len() < pool.capacity {
            available.push_back(resource);
        }
    }
}

/// Get number of available resources in pool
#[no_mangle]
pub extern "C" fn rt_pool_available(handle: i64) -> i64 {
    POOL_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|pool| pool.available.lock().unwrap().len() as i64)
        .unwrap_or(0)
}

/// Get pool capacity
#[no_mangle]
pub extern "C" fn rt_pool_capacity(handle: i64) -> i64 {
    POOL_MAP
        .lock()
        .unwrap()
        .get(&handle)
        .map(|pool| pool.capacity as i64)
        .unwrap_or(0)
}

/// Free resource pool
#[no_mangle]
pub extern "C" fn rt_pool_free(handle: i64) {
    POOL_MAP.lock().unwrap().remove(&handle);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pool_new() {
        let handle = rt_pool_new(10);
        assert!(handle > 0);
        assert_eq!(rt_pool_capacity(handle), 10);
        assert_eq!(rt_pool_available(handle), 0);
        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_release_and_acquire() {
        let handle = rt_pool_new(5);

        let res1 = RuntimeValue::from_int(1);
        let res2 = RuntimeValue::from_int(2);

        rt_pool_release(handle, res1);
        rt_pool_release(handle, res2);

        assert_eq!(rt_pool_available(handle), 2);

        let acquired1 = rt_pool_acquire(handle);
        assert_eq!(acquired1.as_int(), 1); // FIFO order

        let acquired2 = rt_pool_acquire(handle);
        assert_eq!(acquired2.as_int(), 2);

        assert_eq!(rt_pool_available(handle), 0);
        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_acquire_empty() {
        let handle = rt_pool_new(5);

        let val = rt_pool_acquire(handle);
        assert!(val.is_nil());

        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_capacity_limit() {
        let handle = rt_pool_new(3);

        // Release 5 resources (pool capacity is 3)
        for i in 0..5 {
            rt_pool_release(handle, RuntimeValue::from_int(i));
        }

        // Only 3 should be stored
        assert_eq!(rt_pool_available(handle), 3);

        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_reuse() {
        let handle = rt_pool_new(10);

        let res = RuntimeValue::from_int(42);

        // Release and acquire same resource multiple times
        for _ in 0..5 {
            rt_pool_release(handle, res);
            assert_eq!(rt_pool_available(handle), 1);

            let acquired = rt_pool_acquire(handle);
            assert_eq!(acquired.as_int(), 42);
            assert_eq!(rt_pool_available(handle), 0);
        }

        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_multiple_resources() {
        let handle = rt_pool_new(100);

        // Release many resources
        for i in 0..50 {
            rt_pool_release(handle, RuntimeValue::from_int(i));
        }

        assert_eq!(rt_pool_available(handle), 50);

        // Acquire them all
        for i in 0..50 {
            let acquired = rt_pool_acquire(handle);
            assert_eq!(acquired.as_int(), i);
        }

        assert_eq!(rt_pool_available(handle), 0);
        rt_pool_free(handle);
    }

    #[test]
    fn test_pool_invalid_handle() {
        assert_eq!(rt_pool_capacity(999999), 0);
        assert_eq!(rt_pool_available(999999), 0);
        assert!(rt_pool_acquire(999999).is_nil());
        rt_pool_release(999999, RuntimeValue::from_int(42)); // Should not crash
        rt_pool_free(999999); // Should not crash
    }

    #[test]
    fn test_pool_double_free() {
        let handle = rt_pool_new(10);
        rt_pool_free(handle);
        rt_pool_free(handle); // Should be safe
    }

    #[test]
    fn test_pool_zero_capacity() {
        let handle = rt_pool_new(0);

        rt_pool_release(handle, RuntimeValue::from_int(42));
        assert_eq!(rt_pool_available(handle), 0); // Can't store anything

        rt_pool_free(handle);
    }
}
