// Async future operations for monoio state machine integration
// Feature: monoio-direct

use crate::value::monoio_future::{rt_monoio_future_new, IoOperationType, MonoioFuture, PENDING_MARKER};
use crate::value::{HeapObjectType, RuntimeValue};

// Import FFI functions from other modules
use super::tcp::{rt_monoio_tcp_accept, rt_monoio_tcp_connect, rt_monoio_tcp_read, rt_monoio_tcp_write};

// ============================================================================
// Async Future Operations (for state machine integration)
// ============================================================================

/// Poll a MonoioFuture for completion.
///
/// # Arguments
/// * `future` - MonoioFuture to poll
///
/// # Returns
/// - Result value if ready
/// - PENDING_MARKER (-1) if still pending
/// - NIL on error
#[no_mangle]
pub extern "C" fn rt_monoio_poll(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::MonoioFuture {
            return RuntimeValue::NIL;
        }

        let future_ptr = ptr as *const MonoioFuture;

        if (*future_ptr).is_ready() {
            (*future_ptr).result
        } else if (*future_ptr).is_error() {
            (*future_ptr).result
        } else {
            // Still pending
            RuntimeValue::from_int(PENDING_MARKER)
        }
    }
}

/// Create an async TCP read future.
///
/// This returns a MonoioFuture that can be polled for completion.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_read_async(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Create future with I/O operation info
    let future = rt_monoio_future_new(
        stream_id,
        IoOperationType::TcpRead as i64,
        buffer, // Store buffer in context
    );

    // For now, we execute synchronously and store the result
    // Full async would require callback-based completion
    let result = rt_monoio_tcp_read(stream_handle, buffer, max_len);

    // Set the result
    crate::value::monoio_future::rt_monoio_future_set_result(future, result);

    future
}

/// Create an async TCP write future.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_write_async(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let future = rt_monoio_future_new(stream_id, IoOperationType::TcpWrite as i64, buffer);

    let result = rt_monoio_tcp_write(stream_handle, buffer, len);
    crate::value::monoio_future::rt_monoio_future_set_result(future, result);

    future
}

/// Create an async TCP connect future.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_connect_async(addr: RuntimeValue) -> RuntimeValue {
    let future = rt_monoio_future_new(
        0,
        IoOperationType::TcpConnect as i64,
        addr, // Store address in context
    );

    let result = rt_monoio_tcp_connect(addr);
    crate::value::monoio_future::rt_monoio_future_set_result(future, result);

    future
}

/// Create an async TCP accept future.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_accept_async(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    let future = rt_monoio_future_new(listener_id, IoOperationType::TcpAccept as i64, RuntimeValue::NIL);

    let result = rt_monoio_tcp_accept(listener_handle);
    crate::value::monoio_future::rt_monoio_future_set_result(future, result);

    future
}
