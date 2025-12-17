//! Synchronization primitives and FFI functions.
//!
//! This module provides runtime implementations for:
//! - Mutex: Mutual exclusion lock
//! - RwLock: Read-write lock (multiple readers, single writer)
//! - Semaphore: Counting semaphore
//! - Barrier: Synchronization barrier

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier, Condvar, Mutex, RwLock};
use std::time::Duration;

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

// ============================================================================
// Mutex Implementation
// ============================================================================

/// Runtime mutex wrapping a value with mutual exclusion.
#[repr(C)]
pub struct RuntimeMutex {
    pub header: HeapHeader,
    /// The mutex holding the protected value
    pub inner: *mut Arc<Mutex<RuntimeValue>>,
    /// Mutex ID for debugging
    pub mutex_id: u64,
}

static NEXT_MUTEX_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new mutex protecting the given value.
#[no_mangle]
pub extern "C" fn rt_mutex_new(value: RuntimeValue) -> RuntimeValue {
    let mutex_id = NEXT_MUTEX_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(Arc::new(Mutex::new(value))));

    let size = std::mem::size_of::<RuntimeMutex>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeMutex;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Mutex, size as u32);
        (*ptr).inner = inner;
        (*ptr).mutex_id = mutex_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_mutex_ptr(value: RuntimeValue) -> Option<*mut RuntimeMutex> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeMutex;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Lock the mutex and return the protected value.
/// Blocks until the lock is acquired.
#[no_mangle]
pub extern "C" fn rt_mutex_lock(mutex: RuntimeValue) -> RuntimeValue {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*mx_ptr).inner;
        match arc.lock() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL, // Poisoned
        }
    }
}

/// Try to lock the mutex without blocking.
/// Returns the value if lock acquired, NIL otherwise.
#[no_mangle]
pub extern "C" fn rt_mutex_try_lock(mutex: RuntimeValue) -> RuntimeValue {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*mx_ptr).inner;
        match arc.try_lock() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Unlock the mutex and update the protected value.
/// Returns 1 on success, 0 on failure.
#[no_mangle]
pub extern "C" fn rt_mutex_unlock(mutex: RuntimeValue, new_value: RuntimeValue) -> i64 {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return 0;
    };

    unsafe {
        let arc = &*(*mx_ptr).inner;
        match arc.lock() {
            Ok(mut guard) => {
                *guard = new_value;
                1
            }
            Err(_) => 0,
        }
    }
}

/// Get the mutex ID.
#[no_mangle]
pub extern "C" fn rt_mutex_id(mutex: RuntimeValue) -> i64 {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return 0;
    };
    unsafe { (*mx_ptr).mutex_id as i64 }
}

/// Free a mutex.
#[no_mangle]
pub extern "C" fn rt_mutex_free(mutex: RuntimeValue) {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return;
    };

    unsafe {
        if !(*mx_ptr).inner.is_null() {
            drop(Box::from_raw((*mx_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeMutex>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(mx_ptr as *mut u8, layout);
    }
}

include!("sync_rwlock.rs");

include!("sync_semaphore.rs");

include!("sync_barrier.rs");

// ============================================================================
// Unit Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn test_mutex_basic() {
        let val = RuntimeValue::from_int(42);
        let mx = rt_mutex_new(val);
        assert!(mx.is_heap());
        assert!(rt_mutex_id(mx) > 0);

        // Lock and get value
        let locked = rt_mutex_lock(mx);
        assert_eq!(locked.as_int(), 42);

        // Unlock with new value
        let result = rt_mutex_unlock(mx, RuntimeValue::from_int(100));
        assert_eq!(result, 1);

        // Lock again to verify new value
        let locked2 = rt_mutex_lock(mx);
        assert_eq!(locked2.as_int(), 100);

        rt_mutex_free(mx);
    }

    #[test]
    fn test_rwlock_basic() {
        let val = RuntimeValue::from_int(42);
        let rw = rt_rwlock_new(val);
        assert!(rw.is_heap());

        // Read lock
        let read_val = rt_rwlock_read(rw);
        assert_eq!(read_val.as_int(), 42);

        // Write lock and update
        let result = rt_rwlock_set(rw, RuntimeValue::from_int(100));
        assert_eq!(result, 1);

        // Read again
        let read_val2 = rt_rwlock_read(rw);
        assert_eq!(read_val2.as_int(), 100);

        rt_rwlock_free(rw);
    }

    #[test]
    fn test_semaphore_basic() {
        let sem = rt_semaphore_new(2);
        assert!(sem.is_heap());
        assert_eq!(rt_semaphore_count(sem), 2);

        // Acquire twice
        assert_eq!(rt_semaphore_acquire(sem), 1);
        assert_eq!(rt_semaphore_count(sem), 1);
        assert_eq!(rt_semaphore_acquire(sem), 1);
        assert_eq!(rt_semaphore_count(sem), 0);

        // Try acquire should fail (count is 0)
        assert_eq!(rt_semaphore_try_acquire(sem), 0);

        // Release
        assert_eq!(rt_semaphore_release(sem), 1);
        assert_eq!(rt_semaphore_count(sem), 1);

        rt_semaphore_free(sem);
    }

    #[test]
    fn test_barrier_basic() {
        let barrier = rt_barrier_new(1);
        assert!(barrier.is_heap());
        assert_eq!(rt_barrier_thread_count(barrier), 1);

        // Single thread should be leader
        let is_leader = rt_barrier_wait(barrier);
        assert_eq!(is_leader, 1);

        rt_barrier_free(barrier);
    }

    #[test]
    fn test_barrier_invalid() {
        // Invalid thread count
        let barrier = rt_barrier_new(0);
        assert!(barrier.is_nil());

        let barrier2 = rt_barrier_new(-5);
        assert!(barrier2.is_nil());
    }
}
