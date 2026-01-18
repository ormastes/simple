// Monoio TCP networking implementation for Simple language
// Provides async TCP server and client capabilities using io_uring
// Feature: #1745-#1749 (Network I/O - TCP)
//
// MIGRATION NOTE: This module provides backward-compatible wrappers.
// When the `monoio-direct` feature is enabled, all functions delegate to
// the more efficient `rt_monoio_*` implementations in monoio_direct.rs.
// New code should use the `rt_monoio_*` functions directly.

#![cfg(feature = "monoio-net")]

use crate::value::RuntimeValue;
#[cfg(not(feature = "monoio-direct"))]
use crate::monoio_runtime::{execute_async, get_entries, runtime_value_to_string, string_to_runtime_value};
#[cfg(not(feature = "monoio-direct"))]
use std::net::SocketAddr;
#[cfg(not(feature = "monoio-direct"))]
use std::sync::Arc;
#[cfg(not(feature = "monoio-direct"))]
use parking_lot::Mutex;
#[cfg(not(feature = "monoio-direct"))]
use monoio::net::{TcpListener, TcpStream};
#[cfg(not(feature = "monoio-direct"))]
use monoio::io::{AsyncReadRent, AsyncWriteRent};
#[cfg(not(feature = "monoio-direct"))]
use std::time::Duration;

/// NOTE: Monoio wrapper architecture limitation
///
/// Monoio's TcpListener and TcpStream are not Send/Sync, which means they cannot
/// be stored in global static variables. This FFI wrapper uses a simplified approach:
///
/// 1. For listeners: We store only the bind address and recreate the listener for each accept
/// 2. For streams: We store addresses and reconnect for each read/write operation
///
/// This is inefficient but functional for FFI boundaries. For production use,
/// applications should be written in Simple language directly and use the monoio
/// runtime properly (spawn tasks on the runtime, keep streams alive).
///
/// RECOMMENDED: Use the `rt_monoio_*` functions from monoio_direct.rs instead,
/// which properly store and reuse connections via a thread-local IoRegistry.

#[cfg(not(feature = "monoio-direct"))]
/// TCP listener metadata
#[derive(Debug, Clone)]
pub struct MonoioTcpListener {
    addr: SocketAddr,
}

#[cfg(not(feature = "monoio-direct"))]
/// TCP stream metadata
/// Stores connection info; actual I/O reconnects each time
#[derive(Debug, Clone)]
pub struct MonoioTcpStream {
    peer_addr: Option<SocketAddr>,
    local_addr: Option<SocketAddr>,
}

#[cfg(not(feature = "monoio-direct"))]
// Global storage for connection metadata
lazy_static::lazy_static! {
    static ref TCP_LISTENERS: Mutex<Vec<Arc<MonoioTcpListener>>> = Mutex::new(Vec::new());
    static ref TCP_STREAMS: Mutex<Vec<Arc<MonoioTcpStream>>> = Mutex::new(Vec::new());
}

/// Create a TCP listener bound to the specified address
/// Feature #1745: TCP server implementation
///
/// # Arguments
/// * `addr` - RuntimeValue containing address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// RuntimeValue containing listener handle (index), or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    // Delegate to the efficient direct implementation
    crate::monoio_direct::rt_monoio_tcp_listen(addr)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    // Extract string from RuntimeValue
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_tcp_listen: Invalid address argument (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Parse as SocketAddr
    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(addr) => addr,
        Err(e) => {
            tracing::error!("monoio_tcp_listen: Failed to parse address '{}': {}", addr_str, e);
            return RuntimeValue::from_int(-1);
        }
    };

    // Test bind by actually creating a listener (then drop it)
    // Note: monoio's bind() is synchronous, not async
    let bind_result = TcpListener::bind(socket_addr);

    if let Err(e) = bind_result {
        tracing::error!("monoio_tcp_listen: Failed to bind to {}: {}", socket_addr, e);
        return RuntimeValue::from_int(-2); // Connection refused / bind failed
    }

    // Drop the listener immediately since we can't store it
    drop(bind_result);

    // Store listener metadata
    let listener = Arc::new(MonoioTcpListener {
        addr: socket_addr,
    });

    let handle = {
        let mut listeners = TCP_LISTENERS.lock();
        listeners.push(listener);
        (listeners.len() - 1) as i64
    };

    tracing::info!("monoio_tcp_listen: Bound to {} with handle {}", socket_addr, handle);
    RuntimeValue::from_int(handle)
}

/// Accept a connection from a TCP listener
/// Feature #1745: TCP server implementation
///
/// # Arguments
/// * `listener_handle` - RuntimeValue containing listener handle (from monoio_tcp_listen)
///
/// # Returns
/// RuntimeValue containing stream handle (index), or negative value on error/would-block
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_accept(listener_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_accept(listener_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_accept(listener_handle: RuntimeValue) -> RuntimeValue {
    let handle = listener_handle.as_int();

    // Get listener from storage
    let listener_addr = {
        let listeners = TCP_LISTENERS.lock();
        if handle < 0 || handle >= listeners.len() as i64 {
            tracing::error!("monoio_tcp_accept: Invalid listener handle {}", handle);
            return RuntimeValue::from_int(-1);
        }
        listeners[handle as usize].addr
    };

    // Accept connection
    // Note: We have to recreate the listener for each accept (inefficient but necessary for FFI)
    let entries = get_entries();
    let accept_result = execute_async(entries, async move {
        let listener = TcpListener::bind(listener_addr)?;
        let (stream, peer_addr) = listener.accept().await?;
        let local_addr = stream.local_addr()?;
        drop(stream); // We can't store the stream, so drop it
        Ok::<_, std::io::Error>((peer_addr, local_addr))
    });

    match accept_result {
        Ok((peer_addr, local_addr)) => {
            // Store stream metadata
            let stream = Arc::new(MonoioTcpStream {
                peer_addr: Some(peer_addr),
                local_addr: Some(local_addr),
            });

            let stream_handle = {
                let mut streams = TCP_STREAMS.lock();
                streams.push(stream);
                (streams.len() - 1) as i64
            };

            tracing::info!("monoio_tcp_accept: Accepted connection from {} with handle {}", peer_addr, stream_handle);
            RuntimeValue::from_int(stream_handle)
        }
        Err(e) => {
            tracing::error!("monoio_tcp_accept: Failed to accept: {}", e);
            RuntimeValue::from_int(-5) // Would block or I/O error
        }
    }
}

/// Connect to a TCP server at the specified address
/// Feature #1746: TCP client implementation
///
/// # Arguments
/// * `addr` - RuntimeValue containing address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// RuntimeValue containing stream handle (index), or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_connect(addr: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_connect(addr)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_connect(addr: RuntimeValue) -> RuntimeValue {
    // Extract string from RuntimeValue
    let addr_str = match runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("monoio_tcp_connect: Invalid address argument (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    // Parse as SocketAddr
    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(addr) => addr,
        Err(e) => {
            tracing::error!("monoio_tcp_connect: Failed to parse address '{}': {}", addr_str, e);
            return RuntimeValue::from_int(-1);
        }
    };

    // Connect to server
    let entries = get_entries();
    let connect_result = execute_async(entries, async move {
        let stream = TcpStream::connect(socket_addr).await?;
        let peer_addr = stream.peer_addr()?;
        let local_addr = stream.local_addr()?;
        drop(stream); // Can't store the stream across FFI boundary
        Ok::<_, std::io::Error>((peer_addr, local_addr))
    });

    match connect_result {
        Ok((peer_addr, local_addr)) => {
            // Store stream metadata
            let stream = Arc::new(MonoioTcpStream {
                peer_addr: Some(peer_addr),
                local_addr: Some(local_addr),
            });

            let stream_handle = {
                let mut streams = TCP_STREAMS.lock();
                streams.push(stream);
                (streams.len() - 1) as i64
            };

            tracing::info!("monoio_tcp_connect: Connected to {} from {} with handle {}", peer_addr, local_addr, stream_handle);
            RuntimeValue::from_int(stream_handle)
        }
        Err(e) => {
            tracing::error!("monoio_tcp_connect: Failed to connect to {}: {}", socket_addr, e);
            match e.kind() {
                std::io::ErrorKind::ConnectionRefused => RuntimeValue::from_int(-2),
                std::io::ErrorKind::TimedOut => RuntimeValue::from_int(-4),
                _ => RuntimeValue::from_int(-1),
            }
        }
    }
}

/// Read data from a TCP stream into buffer
/// Feature #1747: Zero-copy TCP read
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
/// * `buffer` - RuntimeValue containing buffer (RuntimeArray)
/// * `max_len` - Maximum bytes to read
///
/// # Returns
/// RuntimeValue containing number of bytes read, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_read(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_read(stream_handle, buffer, max_len)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_read(
    _stream_handle: RuntimeValue,
    _buffer: RuntimeValue,
    _max_len: i64,
) -> RuntimeValue {
    // NOT SUPPORTED without monoio-direct feature.
    // Enable monoio-direct feature or use rt_monoio_tcp_read directly.
    tracing::error!("monoio_tcp_read: Enable monoio-direct feature or use rt_monoio_tcp_read");
    RuntimeValue::from_int(-1)
}

/// Write data to a TCP stream from buffer
/// Feature #1748: Zero-copy TCP write
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
/// * `buffer` - RuntimeValue containing buffer (RuntimeArray or RuntimeString)
/// * `len` - Number of bytes to write
///
/// # Returns
/// RuntimeValue containing number of bytes written, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_write(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_write(stream_handle, buffer, len)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_write(
    _stream_handle: RuntimeValue,
    _buffer: RuntimeValue,
    _len: i64,
) -> RuntimeValue {
    tracing::error!("monoio_tcp_write: Enable monoio-direct feature or use rt_monoio_tcp_write");
    RuntimeValue::from_int(-1)
}

/// Flush pending writes on a TCP stream
/// Feature #1748: TCP write operations
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_flush(stream_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_flush(stream_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_flush(_stream_handle: RuntimeValue) -> RuntimeValue {
    tracing::error!("monoio_tcp_flush: Enable monoio-direct feature or use rt_monoio_tcp_flush");
    RuntimeValue::from_int(-1)
}

/// Shutdown a TCP stream for reading, writing, or both
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
/// * `how` - Shutdown mode: 0=Read, 1=Write, 2=Both
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_shutdown(
    stream_handle: RuntimeValue,
    how: i64,
) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_shutdown(stream_handle, how)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_shutdown(
    _stream_handle: RuntimeValue,
    _how: i64,
) -> RuntimeValue {
    tracing::error!("monoio_tcp_shutdown: Enable monoio-direct feature or use rt_monoio_tcp_shutdown");
    RuntimeValue::from_int(-1)
}

/// Close a TCP stream and release resources
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_close(stream_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let handle = stream_handle.as_int();

    // Remove stream from storage
    let mut streams = TCP_STREAMS.lock();
    if handle < 0 || handle >= streams.len() as i64 {
        tracing::error!("monoio_tcp_close: Invalid stream handle {}", handle);
        return RuntimeValue::from_int(-1);
    }

    // Mark as closed by replacing with dummy entry
    // We can't actually remove it (would change other handles' indices)
    streams[handle as usize] = Arc::new(MonoioTcpStream {
        peer_addr: None,
        local_addr: None,
    });

    tracing::info!("monoio_tcp_close: Closed stream handle {}", handle);
    RuntimeValue::from_int(1) // Success
}

/// Close a TCP listener and release resources
/// Feature #1745: TCP server implementation
///
/// # Arguments
/// * `listener_handle` - RuntimeValue containing listener handle
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_listener_close(listener_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let handle = listener_handle.as_int();

    // Remove listener from storage
    let mut listeners = TCP_LISTENERS.lock();
    if handle < 0 || handle >= listeners.len() as i64 {
        tracing::error!("monoio_tcp_listener_close: Invalid listener handle {}", handle);
        return RuntimeValue::from_int(-1);
    }

    // Mark as closed by replacing with dummy entry (using placeholder address)
    // We can't actually remove it (would change other handles' indices)
    use std::net::{IpAddr, Ipv4Addr};
    listeners[handle as usize] = Arc::new(MonoioTcpListener {
        addr: SocketAddr::new(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)), 0),
    });

    tracing::info!("monoio_tcp_listener_close: Closed listener handle {}", handle);
    RuntimeValue::from_int(1) // Success
}

/// Get local address of a TCP stream
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
///
/// # Returns
/// RuntimeValue containing address string, or nil on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_local_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_local_addr(stream_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_local_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let handle = stream_handle.as_int();

    // Get stream from storage
    let local_addr = {
        let streams = TCP_STREAMS.lock();
        if handle < 0 || handle >= streams.len() as i64 {
            tracing::error!("monoio_tcp_local_addr: Invalid stream handle {}", handle);
            return RuntimeValue::NIL;
        }
        streams[handle as usize].local_addr
    };

    match local_addr {
        Some(addr) => {
            let addr_str = addr.to_string();
            tracing::debug!("monoio_tcp_local_addr: handle {} -> {}", handle, addr_str);
            string_to_runtime_value(&addr_str)
        }
        None => {
            tracing::error!("monoio_tcp_local_addr: No local address for handle {}", handle);
            RuntimeValue::NIL
        }
    }
}

/// Get peer address of a TCP stream
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
///
/// # Returns
/// RuntimeValue containing address string, or nil on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_peer_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_peer_addr(stream_handle)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_peer_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let handle = stream_handle.as_int();

    // Get stream from storage
    let peer_addr = {
        let streams = TCP_STREAMS.lock();
        if handle < 0 || handle >= streams.len() as i64 {
            tracing::error!("monoio_tcp_peer_addr: Invalid stream handle {}", handle);
            return RuntimeValue::NIL;
        }
        streams[handle as usize].peer_addr
    };

    match peer_addr {
        Some(addr) => {
            let addr_str = addr.to_string();
            tracing::debug!("monoio_tcp_peer_addr: handle {} -> {}", handle, addr_str);
            string_to_runtime_value(&addr_str)
        }
        None => {
            tracing::error!("monoio_tcp_peer_addr: No peer address for handle {}", handle);
            RuntimeValue::NIL
        }
    }
}

/// Set TCP_NODELAY option (disable Nagle's algorithm)
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
/// * `nodelay` - 1 to enable, 0 to disable
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_set_nodelay(
    stream_handle: RuntimeValue,
    nodelay: i64,
) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_set_nodelay(stream_handle, nodelay)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_set_nodelay(
    _stream_handle: RuntimeValue,
    _nodelay: i64,
) -> RuntimeValue {
    tracing::error!("monoio_tcp_set_nodelay: Enable monoio-direct feature or use rt_monoio_tcp_set_nodelay");
    RuntimeValue::from_int(-1)
}

/// Set TCP keepalive option
/// Feature #1749: TCP connection management
///
/// # Arguments
/// * `stream_handle` - RuntimeValue containing stream handle
/// * `keepalive_secs` - Keepalive interval in seconds, or 0 to disable
///
/// # Returns
/// RuntimeValue containing 1 on success, or negative value on error
#[no_mangle]
#[cfg(feature = "monoio-direct")]
pub extern "C" fn monoio_tcp_set_keepalive(
    stream_handle: RuntimeValue,
    keepalive_secs: i64,
) -> RuntimeValue {
    crate::monoio_direct::rt_monoio_tcp_set_keepalive(stream_handle, keepalive_secs)
}

#[no_mangle]
#[cfg(not(feature = "monoio-direct"))]
pub extern "C" fn monoio_tcp_set_keepalive(
    _stream_handle: RuntimeValue,
    _keepalive_secs: i64,
) -> RuntimeValue {
    tracing::error!("monoio_tcp_set_keepalive: Enable monoio-direct feature or use rt_monoio_tcp_set_keepalive");
    RuntimeValue::from_int(-1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "monoio-direct"))]
    #[test]
    fn test_tcp_structs() {
        use std::net::{IpAddr, Ipv4Addr, SocketAddr};

        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);

        let _listener = MonoioTcpListener { addr };

        let _stream = MonoioTcpStream {
            peer_addr: Some(addr),
            local_addr: None,
        };
    }

    #[test]
    fn test_tcp_listen_invalid_arg() {
        let result = monoio_tcp_listen(RuntimeValue::NIL);
        assert!(result.as_int() < 0); // Should return error for invalid arg
    }

    #[test]
    fn test_tcp_connect_invalid_arg() {
        let result = monoio_tcp_connect(RuntimeValue::NIL);
        assert!(result.as_int() < 0); // Should return error for invalid arg
    }
}
