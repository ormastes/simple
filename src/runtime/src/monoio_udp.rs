// Monoio UDP networking implementation for Simple language
// Provides async UDP socket capabilities using io_uring
// Feature: #1745-#1749 (Network I/O - UDP)

#![cfg(feature = "monoio-net")]

use crate::value::RuntimeValue;
use crate::monoio_runtime::{execute_async, get_entries, runtime_value_to_string, string_to_runtime_value, extract_buffer_bytes, copy_to_buffer};
use std::net::SocketAddr;
use std::sync::Arc;
use parking_lot::Mutex;
use monoio::net::UdpSocket;

/// UDP socket handle stored in RuntimeValue
/// Stores socket metadata including local and optional peer address
///
/// For connected sockets (after monoio_udp_connect), peer_addr is set
/// and send()/recv() can be used instead of send_to()/recv_from()
#[derive(Debug, Clone)]
pub struct MonoioUdpSocket {
    /// Local address the socket is bound to
    local_addr: SocketAddr,
    /// Peer address if socket is connected (for connected UDP)
    peer_addr: Option<SocketAddr>,
}

// Global storage for UDP sockets
// In full implementation, these would be managed by the runtime
lazy_static::lazy_static! {
    static ref UDP_SOCKETS: Mutex<Vec<Arc<MonoioUdpSocket>>> = Mutex::new(Vec::new());
}

/// Create a UDP socket bound to the specified address
/// Feature #1745: UDP socket implementation
///
/// # Arguments
/// * `addr` - RuntimeValue containing address string (e.g., "0.0.0.0:0" for any port)
///
/// # Returns
/// RuntimeValue containing socket handle (index), or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_bind(addr: RuntimeValue) -> RuntimeValue {
    // Extract string from RuntimeValue
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_bind: Invalid address argument (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Parse as SocketAddr
    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(addr) => addr,
        Err(e) => {
            tracing::error!("monoio_udp_bind: Failed to parse address '{}': {}", addr_str, e);
            return RuntimeValue::from_int(-1);
        }
    };

    // Bind socket (synchronous operation in monoio)
    let bind_result = UdpSocket::bind(socket_addr);

    let local_addr = match bind_result {
        Ok(socket) => {
            // Get actual bound address (in case port was 0)
            match socket.local_addr() {
                Ok(addr) => addr,
                Err(e) => {
                    tracing::error!("monoio_udp_bind: Failed to get local address: {}", e);
                    return RuntimeValue::from_int(-1);
                }
            }
            // Drop socket immediately - we'll recreate it for each operation
        }
        Err(e) => {
            tracing::error!("monoio_udp_bind: Failed to bind to {}: {}", socket_addr, e);
            return RuntimeValue::from_int(-2); // Bind failed
        }
    };

    // Store socket metadata
    let socket = Arc::new(MonoioUdpSocket {
        local_addr,
        peer_addr: None,
    });

    let handle = {
        let mut sockets = UDP_SOCKETS.lock();
        sockets.push(socket);
        (sockets.len() - 1) as i64
    };

    tracing::info!("monoio_udp_bind: Bound to {} with handle {}", local_addr, handle);
    RuntimeValue::from_int(handle)
}

/// Send data to a specific address via UDP
/// Feature #1746: UDP send operations
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `buffer` - RuntimeValue containing data to send (RuntimeArray or RuntimeString)
/// * `addr` - RuntimeValue containing destination address string
///
/// # Returns
/// RuntimeValue containing number of bytes sent, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_send_to(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    addr: RuntimeValue,
) -> RuntimeValue {
    let handle = socket_handle.as_int();

    // Get socket's local address
    let local_addr = {
        let sockets = UDP_SOCKETS.lock();
        if handle < 0 || handle >= sockets.len() as i64 {
            tracing::error!("monoio_udp_send_to: Invalid socket handle {}", handle);
            return RuntimeValue::from_int(-1);
        }
        sockets[handle as usize].local_addr
    };

    // Extract destination address
    let dest_addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_udp_send_to: Invalid destination address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let dest_addr: SocketAddr = match dest_addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("monoio_udp_send_to: Failed to parse address '{}': {}", dest_addr_str, e);
            return RuntimeValue::from_int(-1);
        }
    };

    // Extract buffer data
    let data = match extract_buffer_bytes(buffer) {
        Some(d) => d,
        None => {
            tracing::error!("monoio_udp_send_to: Invalid buffer (not a string or array)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Send data using monoio
    let entries = get_entries();
    let send_result = execute_async(entries, async move {
        // Recreate socket at same local address
        let socket = UdpSocket::bind(local_addr)?;

        // Send data
        let (result, _buf) = socket.send_to(data, dest_addr).await;
        result?;

        Ok::<_, std::io::Error>(_buf.len())
    });

    match send_result {
        Ok(bytes_sent) => {
            tracing::debug!("monoio_udp_send_to: Sent {} bytes to {}", bytes_sent, dest_addr);
            RuntimeValue::from_int(bytes_sent as i64)
        }
        Err(e) => {
            tracing::error!("monoio_udp_send_to: Failed to send: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Receive data from UDP socket
/// Feature #1747: UDP receive operations
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `buffer` - RuntimeValue containing buffer for received data
/// * `max_len` - Maximum bytes to receive
///
/// # Returns
/// RuntimeValue containing bytes_received, or negative value on error
///
/// # Notes
/// Currently returns only bytes_received. Sender address is not returned.
/// In future, this could return a tuple (bytes, sender_addr).
/// The received data is written to the provided buffer.
#[no_mangle]
pub extern "C" fn monoio_udp_recv_from(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    let handle = socket_handle.as_int();

    // Get socket's local address
    let local_addr = {
        let sockets = UDP_SOCKETS.lock();
        if handle < 0 || handle >= sockets.len() as i64 {
            tracing::error!("monoio_udp_recv_from: Invalid socket handle {}", handle);
            return RuntimeValue::from_int(-1);
        }
        sockets[handle as usize].local_addr
    };

    if max_len <= 0 {
        tracing::error!("monoio_udp_recv_from: Invalid max_len {}", max_len);
        return RuntimeValue::from_int(-1);
    }

    // Receive data using monoio
    let entries = get_entries();
    let recv_result = execute_async(entries, async move {
        // Recreate socket at same local address
        let socket = UdpSocket::bind(local_addr)?;

        // Allocate receive buffer
        let buf = vec![0u8; max_len as usize];

        // Receive data
        let (result, buf) = socket.recv_from(buf).await;
        let (bytes_read, sender_addr) = result?;

        Ok::<_, std::io::Error>((bytes_read, sender_addr, buf))
    });

    match recv_result {
        Ok((bytes_read, sender_addr, data)) => {
            // Copy received data to RuntimeValue buffer
            let copied = copy_to_buffer(buffer, &data[..bytes_read]);
            if copied < 0 {
                tracing::error!("monoio_udp_recv_from: Failed to copy data to buffer");
                return RuntimeValue::from_int(-1);
            }

            tracing::debug!(
                "monoio_udp_recv_from: Received {} bytes from {}",
                bytes_read,
                sender_addr
            );
            RuntimeValue::from_int(bytes_read as i64)
        }
        Err(e) => {
            tracing::error!("monoio_udp_recv_from: Failed to receive: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Connect UDP socket to a specific peer address
/// Feature #1748: UDP connected sockets
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `addr` - RuntimeValue containing peer address string
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
///
/// # Notes
/// After connecting, send() and recv() can be used instead of send_to() and recv_from()
#[no_mangle]
pub extern "C" fn monoio_udp_connect(
    socket_handle: RuntimeValue,
    addr: RuntimeValue,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_connect from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_connect: deprecated - use rt_monoio_udp_connect instead");
    RuntimeValue::from_int(-1)
}

/// Send data to connected peer via UDP
/// Feature #1748: UDP connected sockets
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle (must be connected)
/// * `buffer` - RuntimeValue containing data to send
///
/// # Returns
/// RuntimeValue containing number of bytes sent, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_send(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_send from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_send: deprecated - use rt_monoio_udp_send instead");
    RuntimeValue::from_int(-1)
}

/// Receive data from connected peer via UDP
/// Feature #1748: UDP connected sockets
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle (must be connected)
/// * `buffer` - RuntimeValue containing buffer for received data
/// * `max_len` - Maximum bytes to receive
///
/// # Returns
/// RuntimeValue containing number of bytes received, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_recv(
    socket_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_recv from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_recv: deprecated - use rt_monoio_udp_recv instead");
    RuntimeValue::from_int(-1)
}

/// Close a UDP socket and release resources
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
///
/// # Notes
/// Due to FFI limitations, this only removes the metadata entry.
/// The actual socket is recreated for each operation.
#[no_mangle]
pub extern "C" fn monoio_udp_close(socket_handle: RuntimeValue) -> RuntimeValue {
    let handle = socket_handle.as_int();

    // Remove socket from storage
    let mut sockets = UDP_SOCKETS.lock();
    if handle < 0 || handle >= sockets.len() as i64 {
        tracing::error!("monoio_udp_close: Invalid socket handle {}", handle);
        return RuntimeValue::from_int(-1);
    }

    // Mark as closed by replacing with dummy entry
    // We can't actually remove it (would change other handles' indices)
    use std::net::{IpAddr, Ipv4Addr};
    sockets[handle as usize] = Arc::new(MonoioUdpSocket {
        local_addr: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)), 0),
        peer_addr: None,
    });

    tracing::info!("monoio_udp_close: Closed socket handle {}", handle);
    RuntimeValue::from_int(1) // Success
}

/// Get local address of a UDP socket
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
///
/// # Returns
/// RuntimeValue containing address string, or nil on error
#[no_mangle]
pub extern "C" fn monoio_udp_local_addr(socket_handle: RuntimeValue) -> RuntimeValue {
    let handle = socket_handle.as_int();

    // Get socket from storage
    let local_addr = {
        let sockets = UDP_SOCKETS.lock();
        if handle < 0 || handle >= sockets.len() as i64 {
            tracing::error!("monoio_udp_local_addr: Invalid socket handle {}", handle);
            return RuntimeValue::NIL;
        }
        sockets[handle as usize].local_addr
    };

    let addr_str = local_addr.to_string();
    tracing::debug!("monoio_udp_local_addr: handle {} -> {}", handle, addr_str);
    string_to_runtime_value(&addr_str)
}

/// Set broadcast option on UDP socket
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `broadcast` - 1 to enable, 0 to disable
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_set_broadcast(
    socket_handle: RuntimeValue,
    broadcast: i64,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_set_broadcast from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_set_broadcast: deprecated - use rt_monoio_udp_set_broadcast instead");
    RuntimeValue::from_int(-1)
}

/// Set multicast TTL on UDP socket
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `ttl` - Time-to-live value (0-255)
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_set_multicast_ttl(
    socket_handle: RuntimeValue,
    ttl: i64,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_set_multicast_ttl from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_set_multicast_ttl: deprecated - use rt_monoio_udp_set_multicast_ttl instead");
    RuntimeValue::from_int(-1)
}

/// Join a multicast group
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `multicast_addr` - RuntimeValue containing multicast address string
/// * `interface_addr` - RuntimeValue containing interface address string
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_join_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_join_multicast from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_join_multicast: deprecated - use rt_monoio_udp_join_multicast instead");
    RuntimeValue::from_int(-1)
}

/// Leave a multicast group
/// Feature #1749: UDP socket management
///
/// # Arguments
/// * `socket_handle` - RuntimeValue containing socket handle
/// * `multicast_addr` - RuntimeValue containing multicast address string
/// * `interface_addr` - RuntimeValue containing interface address string
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
pub extern "C" fn monoio_udp_leave_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    // NOTE: This function is deprecated due to monoio architecture limitations.
    // Use rt_monoio_udp_leave_multicast from monoio_direct.rs instead.

    tracing::warn!("monoio_udp_leave_multicast: deprecated - use rt_monoio_udp_leave_multicast instead");
    RuntimeValue::from_int(-1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_udp_structs() {
        use std::net::{IpAddr, Ipv4Addr};

        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)), 0);

        let _socket = MonoioUdpSocket { local_addr: addr };
    }

    #[test]
    fn test_udp_bind_stub() {
        let result = monoio_udp_bind(RuntimeValue::NIL);
        assert_eq!(result.as_int(), -1);
    }

    #[test]
    fn test_udp_send_to_stub() {
        let result = monoio_udp_send_to(
            RuntimeValue::NIL,
            RuntimeValue::NIL,
            RuntimeValue::NIL,
        );
        assert_eq!(result.as_int(), -1);
    }
}
