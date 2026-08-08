//! Synchronization primitives and SFFI functions.
//!
//! This module provides runtime implementations for:
//! - Atomic: Lock-free atomic operations (#1101)
//! - Mutex: Mutual exclusion lock (#1102)
//! - RwLock: Read-write lock (multiple readers, single writer) (#1103)
//! - Semaphore: Counting semaphore
//! - Barrier: Synchronization barrier

use parking_lot::lock_api::RawMutex as _;
use parking_lot::RawMutex as ParkingRawMutex;
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use std::sync::{Arc, Barrier, Condvar, Mutex, RwLock};
use std::time::Duration;

use super::core::RuntimeValue;
use super::heap::{get_typed_ptr_mut, unregister_heap_ptr, HeapHeader, HeapObjectType};

// ============================================================================
// Atomic Implementation (#1101)
// ============================================================================

/// Runtime atomic wrapper for i64 values.
#[repr(C)]
pub struct RuntimeAtomic {
    pub header: HeapHeader,
    /// The atomic value
    pub value: AtomicI64,
    /// Atomic ID for debugging
    pub atomic_id: u64,
}

static NEXT_ATOMIC_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new atomic value.
#[no_mangle]
pub extern "C" fn rt_atomic_new(initial: i64) -> RuntimeValue {
    let atomic_id = NEXT_ATOMIC_ID.fetch_add(1, Ordering::SeqCst);

    let size = std::mem::size_of::<RuntimeAtomic>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeAtomic;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Atomic, size as u32);
        (*ptr).value = AtomicI64::new(initial);
        (*ptr).atomic_id = atomic_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_atomic_ptr(value: RuntimeValue) -> Option<*mut RuntimeAtomic> {
    get_typed_ptr_mut::<RuntimeAtomic>(value, HeapObjectType::Atomic)
}

/// Atomically load value with Acquire ordering.
#[no_mangle]
pub extern "C" fn rt_atomic_load(atomic: RuntimeValue) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.load(Ordering::Acquire) }
}

/// Atomically store value with Release ordering.
#[no_mangle]
pub extern "C" fn rt_atomic_store(atomic: RuntimeValue, value: i64) {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return;
    };
    unsafe { (*atomic_ptr).value.store(value, Ordering::Release) }
}

/// Atomically swap value with AcqRel ordering.
#[no_mangle]
pub extern "C" fn rt_atomic_swap(atomic: RuntimeValue, value: i64) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.swap(value, Ordering::AcqRel) }
}

/// Atomically compare and exchange.
/// Returns 1 if successful, 0 otherwise. Stores old value in result_ptr.
#[no_mangle]
pub extern "C" fn rt_atomic_compare_exchange(
    atomic: RuntimeValue,
    expected: i64,
    new_value: i64,
    result_ptr: *mut i64,
) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };

    unsafe {
        match (*atomic_ptr)
            .value
            .compare_exchange(expected, new_value, Ordering::AcqRel, Ordering::Acquire)
        {
            Ok(old) => {
                if !result_ptr.is_null() {
                    *result_ptr = old;
                }
                1 // Success
            }
            Err(current) => {
                if !result_ptr.is_null() {
                    *result_ptr = current;
                }
                0 // Failure
            }
        }
    }
}

/// Atomically add and return previous value.
#[no_mangle]
pub extern "C" fn rt_atomic_fetch_add(atomic: RuntimeValue, delta: i64) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.fetch_add(delta, Ordering::AcqRel) }
}

/// Atomically subtract and return previous value.
#[no_mangle]
pub extern "C" fn rt_atomic_fetch_sub(atomic: RuntimeValue, delta: i64) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.fetch_sub(delta, Ordering::AcqRel) }
}

/// Atomically AND and return previous value.
#[no_mangle]
pub extern "C" fn rt_atomic_fetch_and(atomic: RuntimeValue, mask: i64) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.fetch_and(mask, Ordering::AcqRel) }
}

/// Atomically OR and return previous value.
#[no_mangle]
pub extern "C" fn rt_atomic_fetch_or(atomic: RuntimeValue, mask: i64) -> i64 {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return 0;
    };
    unsafe { (*atomic_ptr).value.fetch_or(mask, Ordering::AcqRel) }
}

/// Free atomic.
#[no_mangle]
pub extern "C" fn rt_atomic_free(atomic: RuntimeValue) {
    let Some(atomic_ptr) = as_atomic_ptr(atomic) else {
        return;
    };

    unsafe {
        let size = std::mem::size_of::<RuntimeAtomic>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        unregister_heap_ptr(atomic_ptr as *mut HeapHeader);
        std::alloc::dealloc(atomic_ptr as *mut u8, layout);
    }
}

// ============================================================================
// Mutex Implementation (#1102)
// ============================================================================

/// Runtime mutex wrapping a value with mutual exclusion.
#[repr(C)]
pub struct RuntimeMutex {
    pub header: HeapHeader,
    /// Raw lock held across the explicit Simple lock/unlock calls.
    pub lock: ParkingRawMutex,
    /// Protected value, accessed only while `lock` is held.
    pub value: UnsafeCell<RuntimeValue>,
    /// Process-unique ID of the thread allowed to unlock; zero means unlocked.
    pub owner: AtomicU64,
    /// Mutex ID for debugging
    pub mutex_id: u64,
}

// Safety: `value` is accessed only while `lock` is held, and `owner` prevents
// a foreign thread from ending another thread's explicit lock interval.
unsafe impl Sync for RuntimeMutex {}

static NEXT_MUTEX_ID: AtomicU64 = AtomicU64::new(1);
static NEXT_MUTEX_THREAD_ID: AtomicU64 = AtomicU64::new(1);

fn allocate_mutex_thread_id() -> u64 {
    let id = NEXT_MUTEX_THREAD_ID.fetch_add(1, Ordering::Relaxed);
    assert_ne!(id, 0, "runtime mutex thread ID space exhausted");
    id
}

thread_local! {
    static MUTEX_THREAD_ID: u64 = allocate_mutex_thread_id();
}

fn current_mutex_thread_id() -> u64 {
    MUTEX_THREAD_ID.with(|id| *id)
}

/// Create a new mutex protecting the given value.
#[no_mangle]
pub extern "C" fn rt_mutex_new(value: RuntimeValue) -> RuntimeValue {
    let mutex_id = NEXT_MUTEX_ID.fetch_add(1, Ordering::SeqCst);

    let size = std::mem::size_of::<RuntimeMutex>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeMutex;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        ptr.write(RuntimeMutex {
            header: HeapHeader::new(HeapObjectType::Mutex, size as u32),
            lock: ParkingRawMutex::INIT,
            value: UnsafeCell::new(value),
            owner: AtomicU64::new(0),
            mutex_id,
        });

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_mutex_ptr(value: RuntimeValue) -> Option<*mut RuntimeMutex> {
    get_typed_ptr_mut::<RuntimeMutex>(value, HeapObjectType::Mutex)
}

/// Lock the mutex and return the protected value.
/// Blocks until the lock is acquired.
#[no_mangle]
pub extern "C" fn rt_mutex_lock(mutex: RuntimeValue) -> RuntimeValue {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let mutex = &*mx_ptr;
        mutex.lock.lock();
        mutex.owner.store(current_mutex_thread_id(), Ordering::Release);
        *mutex.value.get()
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
        let mutex = &*mx_ptr;
        if mutex.lock.try_lock() {
            mutex.owner.store(current_mutex_thread_id(), Ordering::Release);
            *mutex.value.get()
        } else {
            RuntimeValue::NIL
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
        let mutex = &*mx_ptr;
        let owner = current_mutex_thread_id();
        if mutex
            .owner
            .compare_exchange(owner, 0, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            return 0;
        }
        *mutex.value.get() = new_value;
        mutex.lock.unlock();
        1
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
/// The caller must ensure no thread can concurrently start using this handle.
#[no_mangle]
pub extern "C" fn rt_mutex_free(mutex: RuntimeValue) {
    let Some(mx_ptr) = as_mutex_ptr(mutex) else {
        return;
    };

    unsafe {
        if (*mx_ptr).owner.load(Ordering::Acquire) != 0 || (*mx_ptr).lock.is_locked() {
            return;
        }
        std::ptr::drop_in_place(mx_ptr);
        let size = std::mem::size_of::<RuntimeMutex>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        unregister_heap_ptr(mx_ptr as *mut HeapHeader);
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

    #[test]
    fn test_atomic_basic() {
        let atomic = rt_atomic_new(42);
        assert!(atomic.is_heap());

        // Load
        assert_eq!(rt_atomic_load(atomic), 42);

        // Store
        rt_atomic_store(atomic, 100);
        assert_eq!(rt_atomic_load(atomic), 100);

        // Swap
        let old = rt_atomic_swap(atomic, 200);
        assert_eq!(old, 100);
        assert_eq!(rt_atomic_load(atomic), 200);

        // Compare exchange (success)
        let mut result = 0i64;
        let success = rt_atomic_compare_exchange(atomic, 200, 300, &mut result as *mut i64);
        assert_eq!(success, 1);
        assert_eq!(result, 200);
        assert_eq!(rt_atomic_load(atomic), 300);

        // Compare exchange (failure)
        let success2 = rt_atomic_compare_exchange(atomic, 999, 400, &mut result as *mut i64);
        assert_eq!(success2, 0);
        assert_eq!(result, 300); // Current value
        assert_eq!(rt_atomic_load(atomic), 300); // Unchanged

        // Fetch add
        let old = rt_atomic_fetch_add(atomic, 50);
        assert_eq!(old, 300);
        assert_eq!(rt_atomic_load(atomic), 350);

        // Fetch sub
        let old = rt_atomic_fetch_sub(atomic, 50);
        assert_eq!(old, 350);
        assert_eq!(rt_atomic_load(atomic), 300);

        // Fetch and
        let old = rt_atomic_fetch_and(atomic, 0xFF);
        assert_eq!(old, 300);
        assert_eq!(rt_atomic_load(atomic), 300 & 0xFF);

        // Fetch or
        rt_atomic_store(atomic, 0x0F);
        let old = rt_atomic_fetch_or(atomic, 0xF0);
        assert_eq!(old, 0x0F);
        assert_eq!(rt_atomic_load(atomic), 0xFF);

        rt_atomic_free(atomic);
    }

    #[test]
    fn test_mutex_basic() {
        let val = RuntimeValue::from_int(42);
        let mx = rt_mutex_new(val);
        assert!(mx.is_heap());
        assert!(rt_mutex_id(mx) > 0);

        // Lock and get value
        let locked = rt_mutex_lock(mx);
        assert_eq!(locked.as_int(), 42);
        assert!(rt_mutex_try_lock(mx).is_nil());

        // Unlock with new value
        let result = rt_mutex_unlock(mx, RuntimeValue::from_int(100));
        assert_eq!(result, 1);

        // Lock again to verify new value
        let locked2 = rt_mutex_lock(mx);
        assert_eq!(locked2.as_int(), 100);
        assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(100)), 1);
        assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(100)), 0);

        rt_mutex_free(mx);
    }

    #[test]
    fn test_mutex_rejects_foreign_unlock_and_holds_waiters() {
        let mx = rt_mutex_new(RuntimeValue::from_int(42));
        assert_eq!(rt_mutex_lock(mx).as_int(), 42);

        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let waiter = std::thread::spawn(move || {
            assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(-1)), 0);
            assert!(rt_mutex_try_lock(mx).is_nil());
            started_tx.send(()).unwrap();
            let value = rt_mutex_lock(mx).as_int();
            assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(101)), 1);
            done_tx.send(value).unwrap();
        });

        started_rx.recv().unwrap();
        assert!(done_rx.recv_timeout(Duration::from_millis(20)).is_err());
        assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(100)), 1);
        assert_eq!(done_rx.recv_timeout(Duration::from_secs(1)).unwrap(), 100);
        waiter.join().unwrap();

        assert_eq!(rt_mutex_lock(mx).as_int(), 101);
        assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(101)), 1);
        rt_mutex_free(mx);
    }

    #[test]
    fn test_mutex_free_refuses_a_held_lock() {
        let mx = rt_mutex_new(RuntimeValue::from_int(7));
        assert_eq!(rt_mutex_lock(mx).as_int(), 7);
        rt_mutex_free(mx);
        assert!(rt_mutex_id(mx) > 0);
        assert_eq!(rt_mutex_unlock(mx, RuntimeValue::from_int(8)), 1);
        rt_mutex_free(mx);
        assert_eq!(rt_mutex_id(mx), 0);
    }

    #[test]
    fn test_low_heap_tagged_values_do_not_crash_mutex_runtime() {
        let null_heap = RuntimeValue::from_raw(0x1);
        let low_heap = RuntimeValue::from_raw(0x9);
        let unregistered_heap = RuntimeValue::from_raw(0x10001);
        let not_mutex = rt_atomic_new(7);

        assert!(rt_mutex_lock(null_heap).is_nil());
        assert!(rt_mutex_try_lock(null_heap).is_nil());
        assert_eq!(rt_mutex_unlock(null_heap, RuntimeValue::from_int(1)), 0);
        assert_eq!(rt_mutex_id(null_heap), 0);

        assert!(rt_mutex_lock(low_heap).is_nil());
        assert!(rt_mutex_lock(unregistered_heap).is_nil());
        assert!(rt_mutex_try_lock(unregistered_heap).is_nil());
        assert_eq!(rt_mutex_unlock(unregistered_heap, RuntimeValue::from_int(1)), 0);
        assert_eq!(rt_mutex_id(unregistered_heap), 0);
        assert!(rt_mutex_try_lock(not_mutex).is_nil());
        assert_eq!(rt_mutex_unlock(not_mutex, RuntimeValue::from_int(1)), 0);
        assert!(rt_rwlock_read(unregistered_heap).is_nil());
        assert!(rt_rwlock_try_read(unregistered_heap).is_nil());
        assert_eq!(rt_rwlock_set(unregistered_heap, RuntimeValue::from_int(1)), 0);
        assert_eq!(rt_semaphore_try_acquire(unregistered_heap), 0);
        assert_eq!(rt_semaphore_release(unregistered_heap), 0);
        assert_eq!(rt_semaphore_count(unregistered_heap), 0);
        assert_eq!(rt_barrier_thread_count(unregistered_heap), 0);

        rt_atomic_free(not_mutex);
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
