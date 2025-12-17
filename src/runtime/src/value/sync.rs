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

// ============================================================================
// RwLock Implementation
// ============================================================================

/// Runtime read-write lock.
#[repr(C)]
pub struct RuntimeRwLock {
    pub header: HeapHeader,
    /// The RwLock holding the protected value
    pub inner: *mut Arc<RwLock<RuntimeValue>>,
    /// Lock ID for debugging
    pub lock_id: u64,
}

static NEXT_RWLOCK_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new RwLock protecting the given value.
#[no_mangle]
pub extern "C" fn rt_rwlock_new(value: RuntimeValue) -> RuntimeValue {
    let lock_id = NEXT_RWLOCK_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(Arc::new(RwLock::new(value))));

    let size = std::mem::size_of::<RuntimeRwLock>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeRwLock;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::RwLock, size as u32);
        (*ptr).inner = inner;
        (*ptr).lock_id = lock_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_rwlock_ptr(value: RuntimeValue) -> Option<*mut RuntimeRwLock> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeRwLock;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Acquire a read lock (shared). Blocks until acquired.
#[no_mangle]
pub extern "C" fn rt_rwlock_read(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.read() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Try to acquire a read lock without blocking.
#[no_mangle]
pub extern "C" fn rt_rwlock_try_read(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.try_read() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Acquire a write lock (exclusive). Blocks until acquired.
#[no_mangle]
pub extern "C" fn rt_rwlock_write(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.write() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Try to acquire a write lock without blocking.
#[no_mangle]
pub extern "C" fn rt_rwlock_try_write(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.try_write() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Update the protected value (must hold write lock).
#[no_mangle]
pub extern "C" fn rt_rwlock_set(lock: RuntimeValue, new_value: RuntimeValue) -> i64 {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return 0;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.write() {
            Ok(mut guard) => {
                *guard = new_value;
                1
            }
            Err(_) => 0,
        }
    }
}

/// Free a RwLock.
#[no_mangle]
pub extern "C" fn rt_rwlock_free(lock: RuntimeValue) {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return;
    };

    unsafe {
        if !(*rw_ptr).inner.is_null() {
            drop(Box::from_raw((*rw_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeRwLock>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(rw_ptr as *mut u8, layout);
    }
}

// ============================================================================
// Semaphore Implementation
// ============================================================================

/// Runtime semaphore (counting semaphore).
#[repr(C)]
pub struct RuntimeSemaphore {
    pub header: HeapHeader,
    /// The semaphore state (count, mutex, condvar)
    pub inner: *mut SemaphoreInner,
    /// Semaphore ID
    pub sem_id: u64,
}

struct SemaphoreInner {
    count: Mutex<i64>,
    condvar: Condvar,
}

static NEXT_SEM_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new semaphore with initial count.
#[no_mangle]
pub extern "C" fn rt_semaphore_new(initial_count: i64) -> RuntimeValue {
    let sem_id = NEXT_SEM_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(SemaphoreInner {
        count: Mutex::new(initial_count.max(0)),
        condvar: Condvar::new(),
    }));

    let size = std::mem::size_of::<RuntimeSemaphore>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeSemaphore;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Semaphore, size as u32);
        (*ptr).inner = inner;
        (*ptr).sem_id = sem_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_semaphore_ptr(value: RuntimeValue) -> Option<*mut RuntimeSemaphore> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeSemaphore;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Acquire the semaphore (decrement count). Blocks if count is 0.
#[no_mangle]
pub extern "C" fn rt_semaphore_acquire(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        while *count <= 0 {
            count = inner.condvar.wait(count).unwrap();
        }
        *count -= 1;
        1
    }
}

/// Try to acquire the semaphore without blocking.
/// Returns 1 if acquired, 0 if would block.
#[no_mangle]
pub extern "C" fn rt_semaphore_try_acquire(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = match inner.count.try_lock() {
            Ok(g) => g,
            Err(_) => return 0,
        };
        if *count > 0 {
            *count -= 1;
            1
        } else {
            0
        }
    }
}

/// Acquire with timeout (milliseconds).
/// Returns 1 if acquired, 0 if timeout.
#[no_mangle]
pub extern "C" fn rt_semaphore_acquire_timeout(sem: RuntimeValue, timeout_ms: i64) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    let timeout = Duration::from_millis(timeout_ms.max(0) as u64);

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        let deadline = std::time::Instant::now() + timeout;

        while *count <= 0 {
            let remaining = deadline.saturating_duration_since(std::time::Instant::now());
            if remaining.is_zero() {
                return 0;
            }
            let (new_count, result) = inner.condvar.wait_timeout(count, remaining).unwrap();
            count = new_count;
            if result.timed_out() && *count <= 0 {
                return 0;
            }
        }
        *count -= 1;
        1
    }
}

/// Release the semaphore (increment count).
#[no_mangle]
pub extern "C" fn rt_semaphore_release(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        *count += 1;
        inner.condvar.notify_one();
        1
    }
}

/// Get current semaphore count.
#[no_mangle]
pub extern "C" fn rt_semaphore_count(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        *inner.count.lock().unwrap()
    }
}

/// Free a semaphore.
#[no_mangle]
pub extern "C" fn rt_semaphore_free(sem: RuntimeValue) {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return;
    };

    unsafe {
        if !(*sem_ptr).inner.is_null() {
            drop(Box::from_raw((*sem_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeSemaphore>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(sem_ptr as *mut u8, layout);
    }
}

// ============================================================================
// Barrier Implementation
// ============================================================================

/// Runtime barrier for synchronizing multiple threads.
#[repr(C)]
pub struct RuntimeBarrier {
    pub header: HeapHeader,
    /// The barrier
    pub inner: *mut Arc<Barrier>,
    /// Barrier ID
    pub barrier_id: u64,
    /// Number of threads to synchronize
    pub thread_count: u64,
}

static NEXT_BARRIER_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new barrier for the given number of threads.
#[no_mangle]
pub extern "C" fn rt_barrier_new(thread_count: i64) -> RuntimeValue {
    if thread_count <= 0 {
        return RuntimeValue::NIL;
    }

    let barrier_id = NEXT_BARRIER_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(Arc::new(Barrier::new(thread_count as usize))));

    let size = std::mem::size_of::<RuntimeBarrier>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeBarrier;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Barrier, size as u32);
        (*ptr).inner = inner;
        (*ptr).barrier_id = barrier_id;
        (*ptr).thread_count = thread_count as u64;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_barrier_ptr(value: RuntimeValue) -> Option<*mut RuntimeBarrier> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeBarrier;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Wait at the barrier. Blocks until all threads arrive.
/// Returns 1 if this is the leader (last to arrive), 0 otherwise.
#[no_mangle]
pub extern "C" fn rt_barrier_wait(barrier: RuntimeValue) -> i64 {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return 0;
    };

    unsafe {
        let arc = &*(*bar_ptr).inner;
        let result = arc.wait();
        if result.is_leader() { 1 } else { 0 }
    }
}

/// Get the thread count for this barrier.
#[no_mangle]
pub extern "C" fn rt_barrier_thread_count(barrier: RuntimeValue) -> i64 {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return 0;
    };

    unsafe { (*bar_ptr).thread_count as i64 }
}

/// Free a barrier.
#[no_mangle]
pub extern "C" fn rt_barrier_free(barrier: RuntimeValue) {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return;
    };

    unsafe {
        if !(*bar_ptr).inner.is_null() {
            drop(Box::from_raw((*bar_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeBarrier>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(bar_ptr as *mut u8, layout);
    }
}

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
