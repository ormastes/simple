// FFI Functions for Monoio Async Executor
// Provides C-compatible interface for the async executor.

#![cfg(feature = "monoio-direct")]

use crate::value::monoio_future::MonoioFuture;
use crate::value::{HeapObjectType, RuntimeValue};
use std::cell::RefCell;

use super::executor::AsyncExecutor;

// ============================================================================
// Thread-Local Executor
// ============================================================================

thread_local! {
    static EXECUTOR: RefCell<AsyncExecutor> = RefCell::new(AsyncExecutor::new());
}

/// Access the thread-local executor
pub fn with_executor<F, R>(f: F) -> R
where
    F: FnOnce(&mut AsyncExecutor) -> R,
{
    EXECUTOR.with(|exec| f(&mut exec.borrow_mut()))
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Initialize the async executor
#[no_mangle]
pub extern "C" fn rt_monoio_async_init(entries: i64) -> RuntimeValue {
    let entries = if entries < 1 || entries > 32768 {
        256
    } else {
        entries as u32
    };

    with_executor(|exec| {
        exec.init(entries);
    });

    RuntimeValue::from_int(1)
}

/// Submit an async TCP accept operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_accept(listener_handle: RuntimeValue, future: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_accept_submit(listener_id, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_accept: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP connect operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_connect(addr: RuntimeValue, future: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_tcp_connect: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_connect_submit(&addr_str, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_connect: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP read operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_read(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
    future: RuntimeValue,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_read_submit(stream_id, buffer, max_len as usize, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_read: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP write operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_write(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
    future: RuntimeValue,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Extract data from buffer
    let data = match crate::monoio_runtime::extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_async_tcp_write: Invalid buffer");
            return RuntimeValue::from_int(-1);
        }
    };

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_write_submit(stream_id, data, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_write: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Poll all pending operations
#[no_mangle]
pub extern "C" fn rt_monoio_async_poll_all() -> RuntimeValue {
    let completed = with_executor(|exec| exec.poll_all());
    RuntimeValue::from_int(completed as i64)
}

/// Poll a single operation by ID
#[no_mangle]
pub extern "C" fn rt_monoio_async_poll_one(op_id: i64) -> RuntimeValue {
    let completed = with_executor(|exec| exec.poll_one(op_id as u64));
    RuntimeValue::from_bool(completed)
}

/// Get the number of pending operations
#[no_mangle]
pub extern "C" fn rt_monoio_async_pending_count() -> RuntimeValue {
    let count = with_executor(|exec| exec.pending_count());
    RuntimeValue::from_int(count as i64)
}

/// TCP listen (synchronous, returns handle)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_tcp_listen: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = with_executor(|exec| exec.tcp_listen(&addr_str));

    match result {
        Ok(id) => RuntimeValue::from_int(id),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_listen: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP stream
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();
    let success = with_executor(|exec| exec.tcp_close(stream_id));
    RuntimeValue::from_bool(success)
}

/// Close a TCP listener
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();
    let success = with_executor(|exec| exec.tcp_listener_close(listener_id));
    RuntimeValue::from_bool(success)
}

/// UDP bind (synchronous, returns handle)
#[no_mangle]
pub extern "C" fn rt_monoio_async_udp_bind(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_udp_bind: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = with_executor(|exec| exec.udp_bind(&addr_str));

    match result {
        Ok(id) => RuntimeValue::from_int(id),
        Err(e) => {
            tracing::error!("rt_monoio_async_udp_bind: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a UDP socket
#[no_mangle]
pub extern "C" fn rt_monoio_async_udp_close(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();
    let success = with_executor(|exec| exec.udp_close(socket_id));
    RuntimeValue::from_bool(success)
}
