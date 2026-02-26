//! Concurrent stack with GC support (Feature #1111).
//!
//! This stack uses a mutex-protected Vec to provide strict LIFO semantics
//! with GC write barriers for safe object management.
//!
//! ## Performance
//!
//! - Push: O(1) amortized, with mutex contention
//! - Pop: O(1), with mutex contention
//! - Write barrier overhead: ~2-5ns per push
//!
//! ## Implementation
//!
//! Uses parking_lot::Mutex for fast locking (2-3x faster than std::sync::Mutex).
//! While not lock-free, this provides strict LIFO semantics which is important
//! for many stack use cases. For truly lock-free access, use ConcurrentQueue instead.

use super::gc_barrier::{GcWriteBarrier, TraceConcurrent};
use crate::value::RuntimeValue;
use parking_lot::Mutex;
use std::sync::Arc;

/// Concurrent stack with GC write barriers.
///
/// This stack is multi-producer multi-consumer (MPMC) and supports
/// storing GC-managed RuntimeValue objects safely. Uses mutex-based
/// synchronization for strict LIFO semantics.
///
/// # Example
///
/// ```ignore
/// use runtime::concurrent::ConcurrentStack;
/// use runtime::value::RuntimeValue;
///
/// let stack = ConcurrentStack::new();
///
/// // Push from multiple threads
/// stack.push(RuntimeValue::from_int(1));
/// stack.push(RuntimeValue::from_int(2));
/// stack.push(RuntimeValue::from_int(3));
///
/// // Pop from multiple threads (strict LIFO order)
/// if let Some(value) = stack.try_pop() {
///     println!("Got: {:?}", value); // 3, then 2, then 1
/// }
/// ```
#[derive(Clone)]
pub struct ConcurrentStack {
    /// Inner vector protected by a fast mutex (parking_lot)
    inner: Arc<Mutex<Vec<RuntimeValue>>>,
}

impl ConcurrentStack {
    /// Create a new empty concurrent stack.
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Create a new concurrent stack with specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(Vec::with_capacity(capacity))),
        }
    }

    /// Push a value onto the stack.
    ///
    /// This operation is thread-safe and provides strict LIFO semantics.
    /// The write barrier ensures the value is visible to the GC.
    #[inline]
    pub fn push(&self, value: RuntimeValue) {
        // Execute write barrier before storing
        GcWriteBarrier::on_write(value);
        self.inner.lock().push(value);
    }

    /// Try to pop a value from the stack.
    ///
    /// Returns `None` if the stack is empty.
    /// This operation is thread-safe and maintains strict LIFO order.
    #[inline]
    pub fn try_pop(&self) -> Option<RuntimeValue> {
        self.inner.lock().pop()
    }

    /// Check if the stack is empty.
    ///
    /// Note: This is inherently racy in a concurrent setting.
    /// The stack may become non-empty immediately after this returns true.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.lock().is_empty()
    }

    /// Get size of the stack.
    ///
    /// This provides a snapshot count at the time of the call.
    /// The actual size may change immediately after.
    pub fn len(&self) -> usize {
        self.inner.lock().len()
    }
}

impl Default for ConcurrentStack {
    fn default() -> Self {
        Self::new()
    }
}

impl TraceConcurrent for ConcurrentStack {
    /// Trace all values in the stack for GC marking.
    ///
    /// Creates a snapshot of all values present at trace time.
    /// This is thread-safe.
    fn trace_snapshot(&self) -> Vec<RuntimeValue> {
        // Clone the vector to get a snapshot
        self.inner.lock().clone()
    }

    fn approximate_len(&self) -> usize {
        self.len()
    }
}

// FFI functions for ConcurrentStack (callable from compiled code)

/// Create a new concurrent stack
#[no_mangle]
pub extern "C" fn simple_concurrent_stack_new() -> *mut ConcurrentStack {
    Box::into_raw(Box::new(ConcurrentStack::new()))
}

/// Destroy a concurrent stack
#[no_mangle]
pub unsafe extern "C" fn simple_concurrent_stack_free(stack: *mut ConcurrentStack) {
    if !stack.is_null() {
        drop(Box::from_raw(stack));
    }
}

/// Push a value onto the stack
#[no_mangle]
pub unsafe extern "C" fn simple_concurrent_stack_push(stack: *mut ConcurrentStack, value: RuntimeValue) {
    if let Some(s) = stack.as_ref() {
        s.push(value);
    }
}

/// Try to pop a value from the stack
///
/// Returns the value, or RuntimeValue::NIL if empty
#[no_mangle]
pub unsafe extern "C" fn simple_concurrent_stack_try_pop(stack: *mut ConcurrentStack) -> RuntimeValue {
    if let Some(s) = stack.as_ref() {
        s.try_pop().unwrap_or(RuntimeValue::NIL)
    } else {
        RuntimeValue::NIL
    }
}

/// Check if stack is empty
#[no_mangle]
pub unsafe extern "C" fn simple_concurrent_stack_is_empty(stack: *mut ConcurrentStack) -> bool {
    if let Some(s) = stack.as_ref() {
        s.is_empty()
    } else {
        true
    }
}

/// Get approximate length
#[no_mangle]
pub unsafe extern "C" fn simple_concurrent_stack_len(stack: *mut ConcurrentStack) -> usize {
    if let Some(s) = stack.as_ref() {
        s.len()
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_basic_operations() {
        let stack = ConcurrentStack::new();
        assert!(stack.is_empty());
        assert_eq!(stack.len(), 0);

        // Push values
        stack.push(RuntimeValue::from_int(1));
        stack.push(RuntimeValue::from_int(2));
        stack.push(RuntimeValue::from_int(3));

        assert!(!stack.is_empty());
        assert_eq!(stack.len(), 3);

        // Pop values (LIFO order)
        assert_eq!(stack.try_pop().unwrap().as_int(), 3);
        assert_eq!(stack.try_pop().unwrap().as_int(), 2);
        assert_eq!(stack.try_pop().unwrap().as_int(), 1);
        assert!(stack.try_pop().is_none());
    }

    #[test]
    fn test_stack_concurrent_access() {
        use std::sync::Arc;
        use std::thread;

        let stack = Arc::new(ConcurrentStack::new());
        let producers = 4;
        let items_per_producer = 100;

        // Spawn producer threads
        let handles: Vec<_> = (0..producers)
            .map(|id| {
                let s = stack.clone();
                thread::spawn(move || {
                    for i in 0..items_per_producer {
                        s.push(RuntimeValue::from_int((id * 1000 + i) as i64));
                    }
                })
            })
            .collect();

        // Wait for producers
        for h in handles {
            h.join().unwrap();
        }

        // Verify all items were pushed
        assert_eq!(stack.len(), producers * items_per_producer);

        // Pop all items
        let mut count = 0;
        while stack.try_pop().is_some() {
            count += 1;
        }
        assert_eq!(count, producers * items_per_producer);
    }

    #[test]
    fn test_trace_snapshot() {
        let stack = ConcurrentStack::new();

        stack.push(RuntimeValue::from_int(10));
        stack.push(RuntimeValue::from_int(20));
        stack.push(RuntimeValue::from_int(30));

        let snapshot = stack.trace_snapshot();
        assert_eq!(snapshot.len(), 3);

        // Stack should still have all values after trace
        assert_eq!(stack.len(), 3);
    }

    #[test]
    fn test_ffi_functions() {
        unsafe {
            let stack = simple_concurrent_stack_new();
            assert!(!stack.is_null());

            assert!(simple_concurrent_stack_is_empty(stack));

            simple_concurrent_stack_push(stack, RuntimeValue::from_int(42));
            assert!(!simple_concurrent_stack_is_empty(stack));
            assert_eq!(simple_concurrent_stack_len(stack), 1);

            let value = simple_concurrent_stack_try_pop(stack);
            assert_eq!(value.as_int(), 42);

            assert!(simple_concurrent_stack_is_empty(stack));

            simple_concurrent_stack_free(stack);
        }
    }
}
