// MonoioFuture heap type for direct monoio async I/O
// Feature: monoio-direct
// Provides zero-overhead async I/O by executing Simple code directly on monoio thread

#![cfg(feature = "monoio-direct")]

use crate::value::heap::{HeapHeader, HeapObjectType};
use crate::value::RuntimeValue;
use std::alloc::{alloc, dealloc, Layout};
use std::ptr;

/// Future state constants
pub const FUTURE_STATE_PENDING: u64 = 0;
pub const FUTURE_STATE_READY: u64 = 1;
pub const FUTURE_STATE_ERROR: u64 = 2;

/// MonoioFuture heap object
///
/// This is a heap-allocated future that can be polled directly on the monoio
/// thread without channel overhead. The inner_future field stores a type-erased
/// pointer to a boxed monoio future.
///
/// # Layout
/// ```text
/// ┌──────────────────────────────────────────────────────────────────┐
/// │ HeapHeader (8 bytes)                                              │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ state: u64 (0=pending, 1=ready, 2=error)                         │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ result: RuntimeValue (8 bytes) - result when ready               │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ waker_state: u64 - pointer to SimpleWaker                        │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ inner_future: u64 - type-erased boxed future pointer             │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ async_state: u64 - state machine state for resumption            │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ ctx: RuntimeValue - captured variables from enclosing scope      │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ io_handle: i64 - I/O resource handle (stream/socket ID)          │
/// ├──────────────────────────────────────────────────────────────────┤
/// │ operation_type: u64 - type of I/O operation                      │
/// └──────────────────────────────────────────────────────────────────┘
/// ```
#[repr(C)]
pub struct MonoioFuture {
    pub header: HeapHeader,
    /// 0 = pending, 1 = ready, 2 = error
    pub state: u64,
    /// Result value (valid when state == READY)
    pub result: RuntimeValue,
    /// Pointer to SimpleWaker (for wakeup notification)
    pub waker_state: u64,
    /// Type-erased pointer to the inner monoio future
    pub inner_future: u64,
    /// State machine state for resumption after await
    pub async_state: u64,
    /// Captured variables from enclosing scope (RuntimeArray)
    pub ctx: RuntimeValue,
    /// I/O resource handle (stream ID, socket ID, etc.)
    pub io_handle: i64,
    /// Type of I/O operation being performed
    pub operation_type: u64,
}

/// I/O operation types
#[repr(u64)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IoOperationType {
    None = 0,
    TcpRead = 1,
    TcpWrite = 2,
    TcpConnect = 3,
    TcpAccept = 4,
    UdpRecv = 5,
    UdpSend = 6,
    UdpRecvFrom = 7,
    UdpSendTo = 8,
}

impl MonoioFuture {
    const SIZE: u32 = std::mem::size_of::<MonoioFuture>() as u32;

    /// Check if the future is pending
    #[inline]
    pub fn is_pending(&self) -> bool {
        self.state == FUTURE_STATE_PENDING
    }

    /// Check if the future is ready
    #[inline]
    pub fn is_ready(&self) -> bool {
        self.state == FUTURE_STATE_READY
    }

    /// Check if the future has an error
    #[inline]
    pub fn is_error(&self) -> bool {
        self.state == FUTURE_STATE_ERROR
    }

    /// Set the result and mark as ready
    #[inline]
    pub fn set_result(&mut self, result: RuntimeValue) {
        self.result = result;
        self.state = FUTURE_STATE_READY;
    }

    /// Set error and mark as error state
    #[inline]
    pub fn set_error(&mut self, error: RuntimeValue) {
        self.result = error;
        self.state = FUTURE_STATE_ERROR;
    }

    /// Get the operation type
    #[inline]
    pub fn get_operation_type(&self) -> IoOperationType {
        match self.operation_type {
            1 => IoOperationType::TcpRead,
            2 => IoOperationType::TcpWrite,
            3 => IoOperationType::TcpConnect,
            4 => IoOperationType::TcpAccept,
            5 => IoOperationType::UdpRecv,
            6 => IoOperationType::UdpSend,
            7 => IoOperationType::UdpRecvFrom,
            8 => IoOperationType::UdpSendTo,
            _ => IoOperationType::None,
        }
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Create a new MonoioFuture
///
/// # Arguments
/// * `io_handle` - I/O resource handle (stream/socket ID)
/// * `operation_type` - Type of I/O operation
/// * `ctx` - Captured context (RuntimeArray or NIL)
///
/// # Returns
/// RuntimeValue containing pointer to new MonoioFuture
#[no_mangle]
pub extern "C" fn rt_monoio_future_new(io_handle: i64, operation_type: i64, ctx: RuntimeValue) -> RuntimeValue {
    let layout = Layout::new::<MonoioFuture>();
    let ptr = unsafe { alloc(layout) as *mut MonoioFuture };

    if ptr.is_null() {
        tracing::error!("rt_monoio_future_new: allocation failed");
        return RuntimeValue::NIL;
    }

    unsafe {
        ptr::write(
            ptr,
            MonoioFuture {
                header: HeapHeader::new(HeapObjectType::MonoioFuture, MonoioFuture::SIZE),
                state: FUTURE_STATE_PENDING,
                result: RuntimeValue::NIL,
                waker_state: 0,
                inner_future: 0,
                async_state: 0,
                ctx,
                io_handle,
                operation_type: operation_type as u64,
            },
        );

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Check if a MonoioFuture is ready
#[no_mangle]
pub extern "C" fn rt_monoio_future_is_ready(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_bool((*future_ptr).is_ready())
    }
}

/// Check if a MonoioFuture is pending
#[no_mangle]
pub extern "C" fn rt_monoio_future_is_pending(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_bool((*future_ptr).is_pending())
    }
}

/// Get the result of a ready MonoioFuture
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_result(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::NIL;
        }

        let future_ptr = ptr as *const MonoioFuture;
        if (*future_ptr).is_ready() || (*future_ptr).is_error() {
            (*future_ptr).result
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Get the state of a MonoioFuture (0=pending, 1=ready, 2=error)
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_state(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::from_int(-1);
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::from_int(-1);
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_int((*future_ptr).state as i64)
    }
}

/// Set the result of a MonoioFuture (marks it as ready)
#[no_mangle]
pub extern "C" fn rt_monoio_future_set_result(future: RuntimeValue, result: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *mut MonoioFuture;
        (*future_ptr).set_result(result);
        RuntimeValue::TRUE
    }
}

/// Set error state on a MonoioFuture
#[no_mangle]
pub extern "C" fn rt_monoio_future_set_error(future: RuntimeValue, error: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *mut MonoioFuture;
        (*future_ptr).set_error(error);
        RuntimeValue::TRUE
    }
}

/// Get the async state (for state machine resumption)
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_async_state(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::from_int(-1);
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::from_int(-1);
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_int((*future_ptr).async_state as i64)
    }
}

/// Set the async state (for state machine resumption)
#[no_mangle]
pub extern "C" fn rt_monoio_future_set_async_state(future: RuntimeValue, state: i64) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *mut MonoioFuture;
        (*future_ptr).async_state = state as u64;
        RuntimeValue::TRUE
    }
}

/// Get the captured context
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_ctx(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::NIL;
        }

        let future_ptr = ptr as *const MonoioFuture;
        (*future_ptr).ctx
    }
}

/// Get the I/O handle
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_io_handle(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::from_int(-1);
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::from_int(-1);
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_int((*future_ptr).io_handle)
    }
}

/// Get the operation type
#[no_mangle]
pub extern "C" fn rt_monoio_future_get_operation_type(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::from_int(-1);
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::from_int(-1);
        }

        let future_ptr = ptr as *const MonoioFuture;
        RuntimeValue::from_int((*future_ptr).operation_type as i64)
    }
}

/// Free a MonoioFuture
#[no_mangle]
pub extern "C" fn rt_monoio_future_free(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::FALSE;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::FALSE;
        }

        let future_ptr = ptr as *mut MonoioFuture;

        // Clean up inner future if present
        if (*future_ptr).inner_future != 0 {
            // The inner future cleanup depends on the operation type
            // For now we just null it out - proper cleanup is done by IoRegistry
            (*future_ptr).inner_future = 0;
        }

        // Clean up waker if present
        if (*future_ptr).waker_state != 0 {
            // Waker cleanup is handled by SimpleWaker
            (*future_ptr).waker_state = 0;
        }

        let layout = Layout::new::<MonoioFuture>();
        dealloc(ptr as *mut u8, layout);
        RuntimeValue::TRUE
    }
}

/// Pending marker value (-1) used to signal that an async operation is still pending
pub const PENDING_MARKER: i64 = -1;

/// Check if a value is the pending marker
#[no_mangle]
pub extern "C" fn rt_monoio_is_pending(value: RuntimeValue) -> RuntimeValue {
    if value.is_int() && value.as_int() == PENDING_MARKER {
        RuntimeValue::TRUE
    } else {
        RuntimeValue::FALSE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monoio_future_new() {
        let future = rt_monoio_future_new(42, 1, RuntimeValue::NIL);
        assert!(future.is_heap());

        let is_pending = rt_monoio_future_is_pending(future);
        assert!(is_pending.as_bool());

        let is_ready = rt_monoio_future_is_ready(future);
        assert!(!is_ready.as_bool());

        rt_monoio_future_free(future);
    }

    #[test]
    fn test_monoio_future_set_result() {
        let future = rt_monoio_future_new(0, 0, RuntimeValue::NIL);

        let result = RuntimeValue::from_int(123);
        rt_monoio_future_set_result(future, result);

        let is_ready = rt_monoio_future_is_ready(future);
        assert!(is_ready.as_bool());

        let got_result = rt_monoio_future_get_result(future);
        assert_eq!(got_result.as_int(), 123);

        rt_monoio_future_free(future);
    }

    #[test]
    fn test_monoio_future_async_state() {
        let future = rt_monoio_future_new(0, 0, RuntimeValue::NIL);

        rt_monoio_future_set_async_state(future, 5);
        let state = rt_monoio_future_get_async_state(future);
        assert_eq!(state.as_int(), 5);

        rt_monoio_future_free(future);
    }
}
