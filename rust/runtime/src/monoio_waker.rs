// SimpleWaker: Bridge between monoio's Waker and Simple's state machine
// Feature: monoio-direct
// Allows monoio futures to wake up Simple async state machines

#![cfg(feature = "monoio-direct")]

use crate::value::RuntimeValue;
use std::sync::Arc;
use std::task::{RawWaker, RawWakerVTable, Waker};

/// SimpleWaker bridges monoio's async wakeup mechanism to Simple's state machine.
///
/// When a monoio I/O operation completes (or needs to be polled again), the
/// waker is used to notify Simple code that it can resume execution.
///
/// # State Machine Integration
///
/// ```text
/// ┌─────────────────────────────────────────────────────────────────┐
/// │ Simple Code (state machine)                                     │
/// │                                                                 │
/// │   state 0: create MonoioFuture, yield                          │
/// │            ▼                                                   │
/// │   state 1: [waker triggered] resume, get result                │
/// └─────────────────────────────────────────────────────────────────┘
///                          ▲
///                          │ wake()
///                          │
/// ┌─────────────────────────────────────────────────────────────────┐
/// │ monoio runtime                                                  │
/// │   - I/O completes                                              │
/// │   - Calls waker.wake()                                         │
/// │   - SimpleWaker updates MonoioFuture state                     │
/// └─────────────────────────────────────────────────────────────────┘
/// ```
pub struct SimpleWaker {
    /// Pointer to the MonoioFuture heap object
    pub future_ptr: *mut crate::value::monoio_future::MonoioFuture,
    /// Function pointer for resuming the Simple state machine
    pub resume_fn: u64,
    /// Wake count (for debugging)
    pub wake_count: std::sync::atomic::AtomicU64,
}

impl SimpleWaker {
    /// Create a new SimpleWaker for a MonoioFuture
    ///
    /// # Safety
    ///
    /// The future_ptr must point to a valid MonoioFuture that will remain
    /// valid for the lifetime of the waker.
    pub unsafe fn new(future_ptr: *mut crate::value::monoio_future::MonoioFuture) -> Arc<Self> {
        Arc::new(Self {
            future_ptr,
            resume_fn: 0,
            wake_count: std::sync::atomic::AtomicU64::new(0),
        })
    }

    /// Create a new SimpleWaker with a resume function
    pub unsafe fn with_resume_fn(
        future_ptr: *mut crate::value::monoio_future::MonoioFuture,
        resume_fn: u64,
    ) -> Arc<Self> {
        Arc::new(Self {
            future_ptr,
            resume_fn,
            wake_count: std::sync::atomic::AtomicU64::new(0),
        })
    }

    /// Convert this SimpleWaker into a std::task::Waker
    pub fn into_waker(self: Arc<Self>) -> Waker {
        unsafe { Waker::from_raw(Self::into_raw_waker(self)) }
    }

    /// Create a RawWaker from an Arc<SimpleWaker>
    fn into_raw_waker(waker: Arc<Self>) -> RawWaker {
        RawWaker::new(Arc::into_raw(waker) as *const (), &SIMPLE_WAKER_VTABLE)
    }

    /// Wake implementation - marks the future as ready
    fn wake(&self) {
        self.wake_count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);

        unsafe {
            if !self.future_ptr.is_null() {
                // Note: We don't mark as ready here because the actual result
                // should be set by the I/O completion handler. The wake just
                // signals that polling should resume.
                tracing::trace!(
                    "SimpleWaker::wake() called for future at {:p}, wake_count={}",
                    self.future_ptr,
                    self.wake_count.load(std::sync::atomic::Ordering::SeqCst)
                );
            }
        }
    }

    /// Get the wake count (for debugging)
    pub fn get_wake_count(&self) -> u64 {
        self.wake_count.load(std::sync::atomic::Ordering::SeqCst)
    }
}

// ============================================================================
// RawWaker VTable Implementation
// ============================================================================

const SIMPLE_WAKER_VTABLE: RawWakerVTable = RawWakerVTable::new(
    // clone
    |ptr| {
        let arc = unsafe { Arc::from_raw(ptr as *const SimpleWaker) };
        let cloned = arc.clone();
        std::mem::forget(arc); // Don't drop the original
        RawWaker::new(Arc::into_raw(cloned) as *const (), &SIMPLE_WAKER_VTABLE)
    },
    // wake (takes ownership)
    |ptr| {
        let arc = unsafe { Arc::from_raw(ptr as *const SimpleWaker) };
        arc.wake();
        // arc is dropped here
    },
    // wake_by_ref (doesn't take ownership)
    |ptr| {
        let arc = unsafe { Arc::from_raw(ptr as *const SimpleWaker) };
        arc.wake();
        std::mem::forget(arc); // Don't drop
    },
    // drop
    |ptr| {
        unsafe { Arc::from_raw(ptr as *const SimpleWaker) };
        // arc is dropped here
    },
);

// ============================================================================
// Context Management
// ============================================================================

/// WakerContext holds the waker for the current async operation.
///
/// This is stored in the MonoioFuture's waker_state field as a raw pointer.
pub struct WakerContext {
    pub waker: Arc<SimpleWaker>,
    /// Whether the operation has been completed
    pub completed: bool,
    /// Result of the operation (if completed)
    pub result: RuntimeValue,
}

impl WakerContext {
    /// Create a new WakerContext
    pub fn new(waker: Arc<SimpleWaker>) -> Self {
        Self {
            waker,
            completed: false,
            result: RuntimeValue::NIL,
        }
    }

    /// Mark as completed with a result
    pub fn complete(&mut self, result: RuntimeValue) {
        self.completed = true;
        self.result = result;
    }

    /// Check if completed
    pub fn is_completed(&self) -> bool {
        self.completed
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Create a waker for a MonoioFuture
#[no_mangle]
pub extern "C" fn rt_monoio_waker_new(future: RuntimeValue) -> RuntimeValue {
    use crate::value::HeapObjectType;
    use crate::value::monoio_future::MonoioFuture;

    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::NIL;
        }

        let future_ptr = ptr as *mut MonoioFuture;
        let waker = SimpleWaker::new(future_ptr);
        let waker_ptr = Arc::into_raw(waker) as u64;

        // Store waker pointer in future
        (*future_ptr).waker_state = waker_ptr;

        RuntimeValue::from_int(waker_ptr as i64)
    }
}

/// Get wake count for a waker (for debugging)
#[no_mangle]
pub extern "C" fn rt_monoio_waker_get_wake_count(waker_ptr: i64) -> RuntimeValue {
    if waker_ptr == 0 {
        return RuntimeValue::from_int(-1);
    }

    unsafe {
        let waker = Arc::from_raw(waker_ptr as *const SimpleWaker);
        let count = waker.get_wake_count();
        std::mem::forget(waker); // Don't drop
        RuntimeValue::from_int(count as i64)
    }
}

/// Free a waker
#[no_mangle]
pub extern "C" fn rt_monoio_waker_free(waker_ptr: i64) -> RuntimeValue {
    if waker_ptr == 0 {
        return RuntimeValue::FALSE;
    }

    unsafe {
        let _waker = Arc::from_raw(waker_ptr as *const SimpleWaker);
        // waker is dropped here
        RuntimeValue::TRUE
    }
}

/// Trigger a waker manually (for testing)
#[no_mangle]
pub extern "C" fn rt_monoio_waker_wake(waker_ptr: i64) -> RuntimeValue {
    if waker_ptr == 0 {
        return RuntimeValue::FALSE;
    }

    unsafe {
        let waker = Arc::from_raw(waker_ptr as *const SimpleWaker);
        waker.wake();
        std::mem::forget(waker); // Don't drop
        RuntimeValue::TRUE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_waker_creation() {
        use crate::value::monoio_future::rt_monoio_future_new;

        let future = rt_monoio_future_new(0, 0, RuntimeValue::NIL);
        let waker_ptr = rt_monoio_waker_new(future);

        assert!(waker_ptr.is_int());
        assert!(waker_ptr.as_int() != 0);

        rt_monoio_waker_free(waker_ptr.as_int());
        crate::value::monoio_future::rt_monoio_future_free(future);
    }

    #[test]
    fn test_simple_waker_wake() {
        use crate::value::monoio_future::rt_monoio_future_new;

        let future = rt_monoio_future_new(0, 0, RuntimeValue::NIL);
        let waker_ptr = rt_monoio_waker_new(future);

        rt_monoio_waker_wake(waker_ptr.as_int());

        let count = rt_monoio_waker_get_wake_count(waker_ptr.as_int());
        assert_eq!(count.as_int(), 1);

        rt_monoio_waker_wake(waker_ptr.as_int());
        let count = rt_monoio_waker_get_wake_count(waker_ptr.as_int());
        assert_eq!(count.as_int(), 2);

        rt_monoio_waker_free(waker_ptr.as_int());
        crate::value::monoio_future::rt_monoio_future_free(future);
    }

    #[test]
    fn test_std_waker_conversion() {
        use std::ptr::null_mut;

        unsafe {
            let waker = SimpleWaker::new(null_mut());
            let std_waker = waker.clone().into_waker();

            // Wake by ref shouldn't panic
            std_waker.wake_by_ref();
            std_waker.wake_by_ref();

            // Clone should work
            let cloned = std_waker.clone();
            cloned.wake_by_ref();

            // Drop should work
            drop(std_waker);
            drop(cloned);
        }
    }
}
