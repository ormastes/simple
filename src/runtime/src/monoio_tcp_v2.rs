// Monoio TCP networking implementation using runtime thread
// Feature: #1745-#1749 (Network I/O - TCP)

#![cfg(feature = "monoio-net")]

use crate::monoio_runtime::{copy_to_buffer, extract_buffer_bytes, runtime_value_to_string};
use crate::monoio_thread::{send_request, IoRequest, IoResponse};
use crate::value::RuntimeValue;

/// Create a TCP listener bound to the specified address
/// Feature #1745: TCP server implementation
#[no_mangle]
pub extern "C" fn monoio_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    // Extract address string
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_tcp_listen: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpListen {
        addr: addr_str.clone(),
        response_tx: std::sync::mpsc::channel().0, // Will be replaced in send_request
    });

    match response {
        IoResponse::Success { id } => {
            tracing::info!(
                "monoio_tcp_listen: Bound to {} with handle {}",
                addr_str,
                id
            );
            RuntimeValue::from_int(id)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_listen: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_listen: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Accept a connection from a TCP listener
/// Feature #1745: TCP server implementation
#[no_mangle]
pub extern "C" fn monoio_tcp_accept(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpAccept {
        listener_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { id } => {
            tracing::info!("monoio_tcp_accept: Accepted connection with handle {}", id);
            RuntimeValue::from_int(id)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_accept: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_accept: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Connect to a TCP server
/// Feature #1746: TCP client implementation
#[no_mangle]
pub extern "C" fn monoio_tcp_connect(addr: RuntimeValue) -> RuntimeValue {
    // Extract address string
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_tcp_connect: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpConnect {
        addr: addr_str.clone(),
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { id } => {
            tracing::info!(
                "monoio_tcp_connect: Connected to {} with handle {}",
                addr_str,
                id
            );
            RuntimeValue::from_int(id)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_connect: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_connect: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Read data from a TCP stream into buffer
/// Feature #1747: Zero-copy TCP read
#[no_mangle]
pub extern "C" fn monoio_tcp_read(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if max_len <= 0 {
        tracing::error!("monoio_tcp_read: Invalid max_len {}", max_len);
        return RuntimeValue::from_int(-1);
    }

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpRead {
        stream_id,
        max_len: max_len as usize,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Data { bytes, len } => {
            // Copy received data into the provided buffer
            let copied = copy_to_buffer(buffer, &bytes);
            if copied < 0 {
                tracing::error!("monoio_tcp_read: Failed to copy data to buffer");
                return RuntimeValue::from_int(-1);
            }

            tracing::debug!(
                "monoio_tcp_read: Read {} bytes, copied {} to buffer",
                len,
                copied
            );
            RuntimeValue::from_int(len as i64)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_read: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_read: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Write data to a TCP stream from buffer
/// Feature #1748: Zero-copy TCP write
#[no_mangle]
pub extern "C" fn monoio_tcp_write(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if len <= 0 {
        tracing::error!("monoio_tcp_write: Invalid len {}", len);
        return RuntimeValue::from_int(-1);
    }

    // Extract data from RuntimeValue buffer
    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            // Truncate to requested length
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!(
                "monoio_tcp_write: Invalid buffer (not a RuntimeArray or RuntimeString)"
            );
            return RuntimeValue::from_int(-1);
        }
    };

    tracing::debug!(
        "monoio_tcp_write: Extracted {} bytes from buffer",
        data.len()
    );

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpWrite {
        stream_id,
        data,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Data { len, .. } => {
            tracing::debug!("monoio_tcp_write: Wrote {} bytes", len);
            RuntimeValue::from_int(len as i64)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_write: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_write: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Flush pending writes
#[no_mangle]
pub extern "C" fn monoio_tcp_flush(_stream_handle: RuntimeValue) -> RuntimeValue {
    // TCP streams auto-flush, no-op
    RuntimeValue::from_int(1)
}

/// Shutdown the write half of a TCP connection
/// how: 0=Read, 1=Write, 2=Both
#[no_mangle]
pub extern "C" fn monoio_tcp_shutdown(stream_handle: RuntimeValue, how: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpShutdown {
        stream_id,
        how,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_tcp_shutdown: Shutdown stream {} with mode {}",
                stream_id,
                how
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_shutdown: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_shutdown: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP stream
#[no_mangle]
pub extern "C" fn monoio_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpClose {
        stream_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::info!("monoio_tcp_close: Closed stream {}", stream_id);
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_close: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_close: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP listener
#[no_mangle]
pub extern "C" fn monoio_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpListenerClose {
        listener_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::info!("monoio_tcp_listener_close: Closed listener {}", listener_id);
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_listener_close: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_listener_close: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Get local address of a TCP stream
#[no_mangle]
pub extern "C" fn monoio_tcp_local_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpGetLocalAddr {
        stream_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Address { addr } => {
            use crate::monoio_runtime::string_to_runtime_value;
            string_to_runtime_value(&addr)
        }
        IoResponse::Error { message, .. } => {
            tracing::error!("monoio_tcp_local_addr: {}", message);
            RuntimeValue::NIL
        }
        _ => {
            tracing::error!("monoio_tcp_local_addr: Unexpected response");
            RuntimeValue::NIL
        }
    }
}

/// Get peer address of a TCP stream
#[no_mangle]
pub extern "C" fn monoio_tcp_peer_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpGetPeerAddr {
        stream_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Address { addr } => {
            use crate::monoio_runtime::string_to_runtime_value;
            string_to_runtime_value(&addr)
        }
        IoResponse::Error { message, .. } => {
            tracing::error!("monoio_tcp_peer_addr: {}", message);
            RuntimeValue::NIL
        }
        _ => {
            tracing::error!("monoio_tcp_peer_addr: Unexpected response");
            RuntimeValue::NIL
        }
    }
}

/// Set TCP_NODELAY option
#[no_mangle]
pub extern "C" fn monoio_tcp_set_nodelay(
    stream_handle: RuntimeValue,
    nodelay: bool,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpSetNodelay {
        stream_id,
        nodelay,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_tcp_set_nodelay: Set nodelay={} for stream {}",
                nodelay,
                stream_id
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_set_nodelay: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_set_nodelay: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Set TCP keepalive option
#[no_mangle]
pub extern "C" fn monoio_tcp_set_keepalive(stream_handle: RuntimeValue, secs: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();
    let secs_opt = if secs > 0 { Some(secs as u32) } else { None };

    // Send request to runtime thread
    let response = send_request(IoRequest::TcpSetKeepalive {
        stream_id,
        secs: secs_opt,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_tcp_set_keepalive: Set keepalive={:?} for stream {}",
                secs_opt,
                stream_id
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_tcp_set_keepalive: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_tcp_set_keepalive: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tcp_listen_invalid_addr() {
        let result = monoio_tcp_listen(RuntimeValue::from_int(123));
        assert_eq!(result.as_int(), -1);
    }
}
