// Monoio UDP networking implementation using runtime thread
// Feature: #1745-#1749 (Network I/O - UDP)

#![cfg(feature = "monoio-net")]

use crate::monoio_runtime::{copy_to_buffer, extract_buffer_bytes, runtime_value_to_string};
use crate::monoio_thread::{send_request, IoRequest, IoResponse};
use crate::value::RuntimeValue;

/// Bind a UDP socket to the specified address
/// Feature #1745: UDP socket creation
#[no_mangle]
pub extern "C" fn monoio_udp_bind(addr: RuntimeValue) -> RuntimeValue {
    // Extract address string
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_bind: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpBind {
        addr: addr_str.clone(),
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { id } => {
            tracing::info!("monoio_udp_bind: Bound to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_bind: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_bind: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Send data to a specific address
/// Feature #1746: UDP send_to
#[no_mangle]
pub extern "C" fn monoio_udp_send_to(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
    addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if len <= 0 {
        tracing::error!("monoio_udp_send_to: Invalid len {}", len);
        return RuntimeValue::from_int(-1);
    }

    // Extract address string
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_send_to: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Extract data from buffer
    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            // Truncate to requested length
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("monoio_udp_send_to: Invalid buffer (not a RuntimeArray or RuntimeString)");
            return RuntimeValue::from_int(-1);
        }
    };

    tracing::debug!("monoio_udp_send_to: Extracted {} bytes from buffer", data.len());

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpSendTo {
        socket_id,
        data,
        addr: addr_str,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Data { len, .. } => {
            tracing::debug!("monoio_udp_send_to: Sent {} bytes", len);
            RuntimeValue::from_int(len as i64)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_send_to: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_send_to: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Receive data from any address
/// Feature #1747: UDP recv_from
///
/// Returns number of bytes received on success, negative error code on failure
/// Note: Peer address is logged but not returned (future enhancement)
#[no_mangle]
pub extern "C" fn monoio_udp_recv_from(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if max_len <= 0 {
        tracing::error!("monoio_udp_recv_from: Invalid max_len {}", max_len);
        return RuntimeValue::from_int(-1);
    }

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpRecvFrom {
        socket_id,
        max_len: max_len as usize,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::DataFrom { bytes, len, addr } => {
            // Copy received data into the provided buffer
            let copied = copy_to_buffer(buffer, &bytes);
            if copied < 0 {
                tracing::error!("monoio_udp_recv_from: Failed to copy data to buffer");
                return RuntimeValue::from_int(-1);
            }

            tracing::debug!(
                "monoio_udp_recv_from: Received {} bytes from {}, copied {} to buffer",
                len,
                addr,
                copied
            );
            RuntimeValue::from_int(len as i64)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_recv_from: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_recv_from: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Connect UDP socket to a peer (for send/recv without address)
#[no_mangle]
pub extern "C" fn monoio_udp_connect(_socket_handle: RuntimeValue, _addr: RuntimeValue) -> RuntimeValue {
    // TODO: [runtime][P1] Implement connected UDP
    tracing::warn!("monoio_udp_connect: Not yet implemented");
    RuntimeValue::from_int(1)
}

/// Send data to connected peer
#[no_mangle]
pub extern "C" fn monoio_udp_send(_socket_handle: RuntimeValue, _buffer: RuntimeValue, _len: i64) -> RuntimeValue {
    // TODO: [runtime][P1] Implement connected send
    tracing::warn!("monoio_udp_send: Not yet implemented");
    RuntimeValue::from_int(-1)
}

/// Receive data from connected peer
#[no_mangle]
pub extern "C" fn monoio_udp_recv(_socket_handle: RuntimeValue, _buffer: RuntimeValue, _max_len: i64) -> RuntimeValue {
    // TODO: [runtime][P1] Implement connected recv
    tracing::warn!("monoio_udp_recv: Not yet implemented");
    RuntimeValue::from_int(-1)
}

/// Close a UDP socket
#[no_mangle]
pub extern "C" fn monoio_udp_close(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpClose {
        socket_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::info!("monoio_udp_close: Closed socket {}", socket_id);
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_close: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_close: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Get local address of a UDP socket
#[no_mangle]
pub extern "C" fn monoio_udp_local_addr(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpGetLocalAddr {
        socket_id,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Address { addr } => {
            use crate::monoio_runtime::string_to_runtime_value;
            string_to_runtime_value(&addr)
        }
        IoResponse::Error { message, .. } => {
            tracing::error!("monoio_udp_local_addr: {}", message);
            RuntimeValue::NIL
        }
        _ => {
            tracing::error!("monoio_udp_local_addr: Unexpected response");
            RuntimeValue::NIL
        }
    }
}

/// Set broadcast option
#[no_mangle]
pub extern "C" fn monoio_udp_set_broadcast(socket_handle: RuntimeValue, broadcast: bool) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpSetBroadcast {
        socket_id,
        broadcast,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_udp_set_broadcast: Set broadcast={} for socket {}",
                broadcast,
                socket_id
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_set_broadcast: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_set_broadcast: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Set multicast TTL
#[no_mangle]
pub extern "C" fn monoio_udp_set_multicast_ttl(socket_handle: RuntimeValue, ttl: i64) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if ttl < 0 || ttl > 255 {
        tracing::error!("monoio_udp_set_multicast_ttl: Invalid TTL {}, must be 0-255", ttl);
        return RuntimeValue::from_int(-1);
    }

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpSetMulticastTtl {
        socket_id,
        ttl: ttl as u32,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!("monoio_udp_set_multicast_ttl: Set TTL={} for socket {}", ttl, socket_id);
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_set_multicast_ttl: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_set_multicast_ttl: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Join multicast group
#[no_mangle]
pub extern "C" fn monoio_udp_join_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    // Extract multicast address string
    let multicast_str = match runtime_value_to_string(multicast_addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_join_multicast: Invalid multicast address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Extract interface address string
    let interface_str = match runtime_value_to_string(interface_addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_join_multicast: Invalid interface address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpJoinMulticast {
        socket_id,
        multicast_addr: multicast_str,
        interface_addr: interface_str,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_udp_join_multicast: Joined multicast group for socket {}",
                socket_id
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_join_multicast: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_join_multicast: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Leave multicast group
#[no_mangle]
pub extern "C" fn monoio_udp_leave_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    // Extract multicast address string
    let multicast_str = match runtime_value_to_string(multicast_addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_leave_multicast: Invalid multicast address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Extract interface address string
    let interface_str = match runtime_value_to_string(interface_addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_leave_multicast: Invalid interface address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send request to runtime thread
    let response = send_request(IoRequest::UdpLeaveMulticast {
        socket_id,
        multicast_addr: multicast_str,
        interface_addr: interface_str,
        response_tx: std::sync::mpsc::channel().0,
    });

    match response {
        IoResponse::Success { .. } => {
            tracing::debug!(
                "monoio_udp_leave_multicast: Left multicast group for socket {}",
                socket_id
            );
            RuntimeValue::from_int(1)
        }
        IoResponse::Error { code, message } => {
            tracing::error!("monoio_udp_leave_multicast: {}", message);
            RuntimeValue::from_int(code)
        }
        _ => {
            tracing::error!("monoio_udp_leave_multicast: Unexpected response");
            RuntimeValue::from_int(-1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_udp_bind_invalid_addr() {
        let result = monoio_udp_bind(RuntimeValue::from_int(123));
        assert_eq!(result.as_int(), -1);
    }
}
