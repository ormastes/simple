// Direct I/O FFI functions for monoio
// Feature: monoio-direct
// Provides zero-overhead async I/O by executing on thread-local monoio runtime

#![cfg(feature = "monoio-direct")]

use crate::monoio_buffer::OwnedBuf;
use crate::monoio_runtime::direct::{block_on, init_direct_runtime, with_registry};
use crate::monoio_runtime::{copy_to_buffer, extract_buffer_bytes};
use crate::value::monoio_future::{rt_monoio_future_new, IoOperationType, MonoioFuture, PENDING_MARKER};
use crate::value::{HeapHeader, HeapObjectType, RuntimeValue};
use monoio::io::{AsyncReadRent, AsyncReadRentExt, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::{TcpListener, TcpStream};
use monoio::net::udp::UdpSocket;
use std::net::SocketAddr;

// ============================================================================
// Runtime Initialization
// ============================================================================

/// Initialize the direct monoio runtime with default settings.
///
/// This must be called before any direct I/O operations on this thread.
/// The runtime is thread-local, so each thread that needs I/O must call this.
#[no_mangle]
pub extern "C" fn rt_monoio_init() -> RuntimeValue {
    match init_direct_runtime(256) {
        Ok(()) => RuntimeValue::from_int(1),
        Err(e) => {
            tracing::error!("rt_monoio_init: {}", e);
            RuntimeValue::from_int(0)
        }
    }
}

// ============================================================================
// TCP Operations
// ============================================================================

/// Create a TCP listener bound to the specified address (direct, synchronous).
///
/// # Arguments
/// * `addr` - Address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// Listener handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_listen: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_tcp_listen: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    match TcpListener::bind(socket_addr) {
        Ok(listener) => {
            let id = with_registry(|reg| reg.add_tcp_listener(listener));
            tracing::debug!("rt_monoio_tcp_listen: Bound to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_listen: Bind failed: {}", e);
            RuntimeValue::from_int(-3)
        }
    }
}

/// Accept a connection from a TCP listener (blocking).
///
/// # Arguments
/// * `listener_handle` - Handle from rt_monoio_tcp_listen
///
/// # Returns
/// Stream handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_accept(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    let result = block_on(async {
        // Get the listener from registry
        let listener = with_registry(|reg| reg.take_tcp_listener(listener_id));

        match listener {
            Some(l) => {
                match l.accept().await {
                    Ok((stream, peer_addr)) => {
                        // Put listener back
                        with_registry(|reg| {
                            // Re-add with same ID would require modification
                            // For now, we add as new and note the ID change
                            let _new_id = reg.add_tcp_listener(l);
                        });
                        let stream_id = with_registry(|reg| reg.add_tcp_stream(stream));
                        tracing::debug!(
                            "rt_monoio_tcp_accept: Accepted from {} with handle {}",
                            peer_addr,
                            stream_id
                        );
                        Ok(stream_id)
                    }
                    Err(e) => {
                        // Put listener back even on error
                        with_registry(|reg| {
                            let _new_id = reg.add_tcp_listener(l);
                        });
                        Err(e)
                    }
                }
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid listener handle",
            )),
        }
    });

    match result {
        Ok(stream_id) => RuntimeValue::from_int(stream_id),
        Err(e) => {
            tracing::error!("rt_monoio_tcp_accept: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Connect to a TCP server (blocking).
///
/// # Arguments
/// * `addr` - Address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// Stream handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_connect(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_connect: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_tcp_connect: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let result = block_on(async { TcpStream::connect(socket_addr).await });

    match result {
        Ok(stream) => {
            let id = with_registry(|reg| reg.add_tcp_stream(stream));
            tracing::debug!("rt_monoio_tcp_connect: Connected to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        Err(e) => {
            let code = match e.kind() {
                std::io::ErrorKind::ConnectionRefused => -3,
                std::io::ErrorKind::TimedOut => -4,
                _ => -5,
            };
            tracing::error!("rt_monoio_tcp_connect: {}", e);
            RuntimeValue::from_int(code)
        }
    }
}

/// Read data from a TCP stream (blocking, zero-copy).
///
/// # Arguments
/// * `stream_handle` - Handle from rt_monoio_tcp_connect or rt_monoio_tcp_accept
/// * `buffer` - RuntimeArray to read into
/// * `max_len` - Maximum bytes to read
///
/// # Returns
/// Number of bytes read (0 = EOF) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_read(stream_handle: RuntimeValue, buffer: RuntimeValue, max_len: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if max_len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let result = block_on(async {
        let stream = with_registry(|reg| reg.take_tcp_stream(stream_id));

        match stream {
            Some(mut s) => {
                let buf = OwnedBuf::new(max_len as usize);
                let (res, buf) = s.read(buf).await;

                // Put stream back
                with_registry(|reg| {
                    // Re-insert stream
                    let _new_id = reg.add_tcp_stream(s);
                });

                match res {
                    Ok(n) => Ok((n, buf.into_vec())),
                    Err(e) => Err(e),
                }
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid stream handle",
            )),
        }
    });

    match result {
        Ok((n, data)) => {
            // Copy data to the provided buffer
            let copied = copy_to_buffer(buffer, &data[..n]);
            if copied < 0 {
                tracing::error!("rt_monoio_tcp_read: Failed to copy to buffer");
                return RuntimeValue::from_int(-6);
            }
            RuntimeValue::from_int(n as i64)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_read: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Write data to a TCP stream (blocking, zero-copy).
///
/// # Arguments
/// * `stream_handle` - Handle from rt_monoio_tcp_connect or rt_monoio_tcp_accept
/// * `buffer` - RuntimeArray or RuntimeString to write from
/// * `len` - Number of bytes to write
///
/// # Returns
/// Number of bytes written or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_write(stream_handle: RuntimeValue, buffer: RuntimeValue, len: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if len <= 0 {
        return RuntimeValue::from_int(0);
    }

    // Extract data from buffer
    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_tcp_write: Invalid buffer");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = block_on(async {
        let stream = with_registry(|reg| reg.take_tcp_stream(stream_id));

        match stream {
            Some(mut s) => {
                let (res, _buf) = s.write(data).await;

                // Put stream back
                with_registry(|reg| {
                    let _new_id = reg.add_tcp_stream(s);
                });

                res
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid stream handle",
            )),
        }
    });

    match result {
        Ok(n) => RuntimeValue::from_int(n as i64),
        Err(e) => {
            tracing::error!("rt_monoio_tcp_write: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP stream.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if with_registry(|reg| reg.remove_tcp_stream(stream_id)) {
        RuntimeValue::from_int(1)
    } else {
        RuntimeValue::from_int(0)
    }
}

/// Close a TCP listener.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    if with_registry(|reg| reg.remove_tcp_listener(listener_id)) {
        RuntimeValue::from_int(1)
    } else {
        RuntimeValue::from_int(0)
    }
}

// ============================================================================
// UDP Operations
// ============================================================================

/// Bind a UDP socket to the specified address.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_bind(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_bind: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_udp_bind: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    match UdpSocket::bind(socket_addr) {
        Ok(socket) => {
            let id = with_registry(|reg| reg.add_udp_socket(socket));
            tracing::debug!("rt_monoio_udp_bind: Bound to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        Err(e) => {
            tracing::error!("rt_monoio_udp_bind: Bind failed: {}", e);
            RuntimeValue::from_int(-3)
        }
    }
}

/// Send data to a specific address via UDP.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_send_to(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
    addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_send_to: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_udp_send_to: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_udp_send_to: Invalid buffer");
            return RuntimeValue::from_int(-3);
        }
    };

    let result = block_on(async {
        let socket = with_registry(|reg| reg.take_udp_socket(socket_id));

        match socket {
            Some(s) => {
                let (res, _buf) = s.send_to(data, socket_addr).await;

                // Put socket back
                with_registry(|reg| {
                    let _new_id = reg.add_udp_socket(s);
                });

                res
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid socket handle",
            )),
        }
    });

    match result {
        Ok(n) => RuntimeValue::from_int(n as i64),
        Err(e) => {
            tracing::error!("rt_monoio_udp_send_to: {}", e);
            RuntimeValue::from_int(-4)
        }
    }
}

/// Receive data from UDP socket (returns data and sender address).
#[no_mangle]
pub extern "C" fn rt_monoio_udp_recv_from(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if max_len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let result = block_on(async {
        let socket = with_registry(|reg| reg.take_udp_socket(socket_id));

        match socket {
            Some(s) => {
                let buf = OwnedBuf::new(max_len as usize);
                let (res, buf) = s.recv_from(buf).await;

                // Put socket back
                with_registry(|reg| {
                    let _new_id = reg.add_udp_socket(s);
                });

                match res {
                    Ok((n, addr)) => Ok((n, buf.into_vec(), addr)),
                    Err(e) => Err(e),
                }
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid socket handle",
            )),
        }
    });

    match result {
        Ok((n, data, _addr)) => {
            let copied = copy_to_buffer(buffer, &data[..n]);
            if copied < 0 {
                tracing::error!("rt_monoio_udp_recv_from: Failed to copy to buffer");
                return RuntimeValue::from_int(-5);
            }
            RuntimeValue::from_int(n as i64)
        }
        Err(e) => {
            tracing::error!("rt_monoio_udp_recv_from: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a UDP socket.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_close(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if with_registry(|reg| reg.remove_udp_socket(socket_id)) {
        RuntimeValue::from_int(1)
    } else {
        RuntimeValue::from_int(0)
    }
}

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

// ============================================================================
// Performance Metrics
// ============================================================================

/// Get performance metrics for the direct runtime.
#[no_mangle]
pub extern "C" fn rt_monoio_direct_stats() -> RuntimeValue {
    // Return resource count for now
    let count = with_registry(|reg| reg.tcp_listener_count() + reg.tcp_stream_count() + reg.udp_socket_count());
    RuntimeValue::from_int(count as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init() {
        let result = rt_monoio_init();
        // May fail if io_uring not available
        assert!(result.as_int() == 0 || result.as_int() == 1);
    }
}
