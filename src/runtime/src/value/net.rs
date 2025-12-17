//! Networking FFI functions for TCP, UDP, and HTTP.
//!
//! This module provides the native implementations for the Simple language's
//! networking APIs. Sockets are managed via numeric handles stored in a
//! global registry.

use lazy_static::lazy_static;
use socket2::Socket;
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;
use std::time::Duration;

// ============================================================================
// Error codes
// ============================================================================

/// Error codes returned by networking functions
#[repr(i64)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetError {
    Success = 0,
    /// Address already in use
    AddrInUse = 1,
    /// Address not available
    AddrNotAvailable = 2,
    /// Connection refused
    ConnectionRefused = 3,
    /// Connection reset
    ConnectionReset = 4,
    /// Connection aborted
    ConnectionAborted = 5,
    /// Network unreachable
    NetworkUnreachable = 6,
    /// Host unreachable
    HostUnreachable = 7,
    /// Operation timed out
    TimedOut = 8,
    /// Operation would block
    WouldBlock = 9,
    /// Permission denied
    PermissionDenied = 10,
    /// Invalid input/argument
    InvalidInput = 11,
    /// Not connected
    NotConnected = 12,
    /// Already connected
    AlreadyConnected = 13,
    /// Broken pipe
    BrokenPipe = 14,
    /// Unexpected EOF
    UnexpectedEof = 15,
    /// Invalid handle
    InvalidHandle = 100,
    /// Invalid address format
    InvalidAddress = 101,
    /// HTTP error
    HttpError = 200,
    /// HTTP invalid URL
    HttpInvalidUrl = 201,
    /// HTTP too many redirects
    HttpTooManyRedirects = 202,
    /// HTTP invalid response
    HttpInvalidResponse = 203,
    /// TLS/SSL error
    TlsError = 204,
    /// Unknown error
    Unknown = 255,
}

impl From<std::io::Error> for NetError {
    fn from(err: std::io::Error) -> Self {
        use std::io::ErrorKind;
        match err.kind() {
            ErrorKind::AddrInUse => NetError::AddrInUse,
            ErrorKind::AddrNotAvailable => NetError::AddrNotAvailable,
            ErrorKind::ConnectionRefused => NetError::ConnectionRefused,
            ErrorKind::ConnectionReset => NetError::ConnectionReset,
            ErrorKind::ConnectionAborted => NetError::ConnectionAborted,
            ErrorKind::NetworkUnreachable => NetError::NetworkUnreachable,
            ErrorKind::HostUnreachable => NetError::HostUnreachable,
            ErrorKind::TimedOut => NetError::TimedOut,
            ErrorKind::WouldBlock => NetError::WouldBlock,
            ErrorKind::PermissionDenied => NetError::PermissionDenied,
            ErrorKind::InvalidInput => NetError::InvalidInput,
            ErrorKind::NotConnected => NetError::NotConnected,
            ErrorKind::AlreadyExists => NetError::AlreadyConnected,
            ErrorKind::BrokenPipe => NetError::BrokenPipe,
            ErrorKind::UnexpectedEof => NetError::UnexpectedEof,
            _ => NetError::Unknown,
        }
    }
}

// ============================================================================
// Socket handle registry
// ============================================================================

/// Type of socket stored in the registry
enum SocketEntry {
    TcpListener(TcpListener),
    TcpStream(TcpStream),
    UdpSocket(UdpSocket),
}

lazy_static! {
    /// Global socket registry mapping handles to socket objects
    static ref SOCKET_REGISTRY: Mutex<HashMap<i64, SocketEntry>> = Mutex::new(HashMap::new());
    /// Counter for generating unique handles
    static ref NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);
}

/// Allocate a new handle for a socket
fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Register a TCP listener and return its handle
fn register_tcp_listener(listener: TcpListener) -> i64 {
    let handle = alloc_handle();
    SOCKET_REGISTRY
        .lock()
        .unwrap()
        .insert(handle, SocketEntry::TcpListener(listener));
    handle
}

/// Register a TCP stream and return its handle
fn register_tcp_stream(stream: TcpStream) -> i64 {
    let handle = alloc_handle();
    SOCKET_REGISTRY
        .lock()
        .unwrap()
        .insert(handle, SocketEntry::TcpStream(stream));
    handle
}

/// Register a UDP socket and return its handle
fn register_udp_socket(socket: UdpSocket) -> i64 {
    let handle = alloc_handle();
    SOCKET_REGISTRY
        .lock()
        .unwrap()
        .insert(handle, SocketEntry::UdpSocket(socket));
    handle
}

/// Remove a socket from the registry
fn unregister_socket(handle: i64) -> Option<SocketEntry> {
    SOCKET_REGISTRY.lock().unwrap().remove(&handle)
}

// ============================================================================
// Address parsing utilities
// ============================================================================

/// Parse a socket address from raw pointer and length
/// Format: "ip:port" or "[ipv6]:port"
unsafe fn parse_socket_addr(addr_ptr: i64, addr_len: i64) -> Result<SocketAddr, NetError> {
    if addr_ptr == 0 || addr_len <= 0 {
        return Err(NetError::InvalidAddress);
    }
    let slice = std::slice::from_raw_parts(addr_ptr as *const u8, addr_len as usize);
    let addr_str = std::str::from_utf8(slice).map_err(|_| NetError::InvalidAddress)?;
    addr_str.parse().map_err(|_| NetError::InvalidAddress)
}

/// Allocate and return a string representation of a socket address
/// Returns a pointer to the string (caller must free)
fn addr_to_string_ptr(addr: &SocketAddr) -> i64 {
    let s = addr.to_string();
    let boxed = s.into_boxed_str();
    let ptr = Box::into_raw(boxed) as *const str as *const u8 as i64;
    ptr
}

// ============================================================================
// TCP FFI functions
// ============================================================================

/// Bind a TCP listener to an address.
/// Returns (handle, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64) {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return (0, e as i64),
    };

    match TcpListener::bind(addr) {
        Ok(listener) => {
            let handle = register_tcp_listener(listener);
            (handle, NetError::Success as i64)
        }
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Accept an incoming TCP connection.
/// Returns (stream_handle, peer_addr_ptr, error_code)
#[no_mangle]
pub extern "C" fn native_tcp_accept(handle: i64) -> (i64, i64, i64) {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, 0, NetError::InvalidHandle as i64),
    };

    let listener = match entry {
        SocketEntry::TcpListener(l) => l,
        _ => return (0, 0, NetError::InvalidHandle as i64),
    };

    match listener.accept() {
        Ok((stream, peer_addr)) => {
            drop(registry); // Release lock before registering
            let stream_handle = register_tcp_stream(stream);
            let addr_ptr = addr_to_string_ptr(&peer_addr);
            (stream_handle, addr_ptr, NetError::Success as i64)
        }
        Err(e) => (0, 0, NetError::from(e) as i64),
    }
}

/// Connect to a remote TCP address.
/// Returns (handle, local_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_connect(addr_ptr: i64, addr_len: i64) -> (i64, i64, i64) {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return (0, 0, e as i64),
    };

    match TcpStream::connect(addr) {
        Ok(stream) => {
            let local_addr = stream.local_addr().ok();
            let handle = register_tcp_stream(stream);
            let local_ptr = local_addr.map(|a| addr_to_string_ptr(&a)).unwrap_or(0);
            (handle, local_ptr, NetError::Success as i64)
        }
        Err(e) => (0, 0, NetError::from(e) as i64),
    }
}

/// Connect to a remote TCP address with timeout.
/// Returns (handle, local_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_connect_timeout(
    addr_ptr: i64,
    addr_len: i64,
    timeout_ns: i64,
) -> (i64, i64, i64) {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return (0, 0, e as i64),
    };

    let timeout = if timeout_ns > 0 {
        Duration::from_nanos(timeout_ns as u64)
    } else {
        Duration::from_secs(30) // Default 30 second timeout
    };

    match TcpStream::connect_timeout(&addr, timeout) {
        Ok(stream) => {
            let local_addr = stream.local_addr().ok();
            let handle = register_tcp_stream(stream);
            let local_ptr = local_addr.map(|a| addr_to_string_ptr(&a)).unwrap_or(0);
            (handle, local_ptr, NetError::Success as i64)
        }
        Err(e) => (0, 0, NetError::from(e) as i64),
    }
}

/// Read data from a TCP stream.
/// Returns (bytes_read, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_read(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let mut registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get_mut(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match stream.read(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Write data to a TCP stream.
/// Returns (bytes_written, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_write(
    handle: i64,
    data_ptr: i64,
    data_len: i64,
) -> (i64, i64) {
    if data_ptr == 0 || data_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let mut registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get_mut(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
    match stream.write(data) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Flush a TCP stream's output buffer.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_flush(handle: i64) -> i64 {
    let mut registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get_mut(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match stream.flush() {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Shutdown a TCP stream (0=read, 1=write, 2=both).
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_shutdown(handle: i64, how: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let shutdown = match how {
        0 => std::net::Shutdown::Read,
        1 => std::net::Shutdown::Write,
        _ => std::net::Shutdown::Both,
    };

    match stream.shutdown(shutdown) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Close a TCP socket (listener or stream).
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_close(handle: i64) -> i64 {
    match unregister_socket(handle) {
        Some(_) => NetError::Success as i64,
        None => NetError::InvalidHandle as i64,
    }
}

/// Set the connection backlog for a TCP listener.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_backlog(_handle: i64, _backlog: i64) -> i64 {
    // Note: Rust's TcpListener doesn't expose backlog setting after bind.
    // This would require using socket2 for more control.
    // For now, this is a no-op (backlog is set at bind time).
    NetError::Success as i64
}

/// Set TCP_NODELAY option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_nodelay(handle: i64, nodelay: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match stream.set_nodelay(nodelay != 0) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set keepalive option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_keepalive(handle: i64, keepalive_ns: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    // Convert to socket2 for keepalive control
    // keepalive_ns > 0 means enable, 0 means disable
    let socket = Socket::from(stream.try_clone().unwrap());
    let enable = keepalive_ns > 0;

    match socket.set_keepalive(enable) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set read timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_read_timeout(handle: i64, timeout_ns: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let timeout = if timeout_ns > 0 {
        Some(Duration::from_nanos(timeout_ns as u64))
    } else {
        None
    };

    match stream.set_read_timeout(timeout) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set write timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_write_timeout(handle: i64, timeout_ns: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let timeout = if timeout_ns > 0 {
        Some(Duration::from_nanos(timeout_ns as u64))
    } else {
        None
    };

    match stream.set_write_timeout(timeout) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Get TCP_NODELAY option.
/// Returns (nodelay, error_code)
#[no_mangle]
pub extern "C" fn native_tcp_get_nodelay(handle: i64) -> (i64, i64) {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    match stream.nodelay() {
        Ok(nodelay) => (if nodelay { 1 } else { 0 }, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Peek data from a TCP stream without consuming it.
/// Returns (bytes_peeked, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let stream = match entry {
        SocketEntry::TcpStream(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match stream.peek(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

// ============================================================================
// UDP FFI functions
// ============================================================================

/// Bind a UDP socket to an address.
/// Returns (handle, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64) {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return (0, e as i64),
    };

    match UdpSocket::bind(addr) {
        Ok(socket) => {
            let handle = register_udp_socket(socket);
            (handle, NetError::Success as i64)
        }
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Connect a UDP socket to a remote address (sets default destination).
/// Returns error_code
#[no_mangle]
pub unsafe extern "C" fn native_udp_connect(handle: i64, addr_ptr: i64, addr_len: i64) -> i64 {
    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return e as i64,
    };

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match socket.connect(addr) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Receive data from a UDP socket with source address.
/// Returns (bytes_recv, peer_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_recv_from(
    handle: i64,
    buf_ptr: i64,
    buf_len: i64,
) -> (i64, i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, 0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, 0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, 0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.recv_from(buf) {
        Ok((n, addr)) => {
            let addr_ptr = addr_to_string_ptr(&addr);
            (n as i64, addr_ptr, NetError::Success as i64)
        }
        Err(e) => (0, 0, NetError::from(e) as i64),
    }
}

/// Receive data from a connected UDP socket.
/// Returns (bytes_recv, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_recv(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.recv(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Send data to a specific address.
/// Returns (bytes_sent, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_send_to(
    handle: i64,
    data_ptr: i64,
    data_len: i64,
    addr_ptr: i64,
    addr_len: i64,
) -> (i64, i64) {
    if data_ptr == 0 || data_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let addr = match parse_socket_addr(addr_ptr, addr_len) {
        Ok(a) => a,
        Err(e) => return (0, e as i64),
    };

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
    match socket.send_to(data, addr) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Send data on a connected UDP socket.
/// Returns (bytes_sent, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_send(
    handle: i64,
    data_ptr: i64,
    data_len: i64,
) -> (i64, i64) {
    if data_ptr == 0 || data_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
    match socket.send(data) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Peek data from a UDP socket with source address.
/// Returns (bytes_peeked, peer_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_peek_from(
    handle: i64,
    buf_ptr: i64,
    buf_len: i64,
) -> (i64, i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, 0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, 0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, 0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.peek_from(buf) {
        Ok((n, addr)) => {
            let addr_ptr = addr_to_string_ptr(&addr);
            (n as i64, addr_ptr, NetError::Success as i64)
        }
        Err(e) => (0, 0, NetError::from(e) as i64),
    }
}

/// Peek data from a connected UDP socket.
/// Returns (bytes_peeked, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    if buf_ptr == 0 || buf_len <= 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
    match socket.peek(buf) {
        Ok(n) => (n as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Get the connected peer address of a UDP socket.
/// Returns (addr_ptr, error_code)
#[no_mangle]
pub extern "C" fn native_udp_peer_addr(handle: i64) -> (i64, i64) {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    match socket.peer_addr() {
        Ok(addr) => {
            let addr_ptr = addr_to_string_ptr(&addr);
            (addr_ptr, NetError::Success as i64)
        }
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Set broadcast option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_broadcast(handle: i64, broadcast: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match socket.set_broadcast(broadcast != 0) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set multicast loop option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_multicast_loop(handle: i64, on: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    // Try IPv4 first, then IPv6
    if socket.set_multicast_loop_v4(on != 0).is_ok() {
        return NetError::Success as i64;
    }
    match socket.set_multicast_loop_v6(on != 0) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set multicast TTL.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_multicast_ttl(handle: i64, ttl: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match socket.set_multicast_ttl_v4(ttl as u32) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set TTL.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_ttl(handle: i64, ttl: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    match socket.set_ttl(ttl as u32) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set read timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_read_timeout(handle: i64, timeout_ns: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let timeout = if timeout_ns > 0 {
        Some(Duration::from_nanos(timeout_ns as u64))
    } else {
        None
    };

    match socket.set_read_timeout(timeout) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Set write timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_write_timeout(handle: i64, timeout_ns: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let timeout = if timeout_ns > 0 {
        Some(Duration::from_nanos(timeout_ns as u64))
    } else {
        None
    };

    match socket.set_write_timeout(timeout) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Get broadcast option.
/// Returns (broadcast, error_code)
#[no_mangle]
pub extern "C" fn native_udp_get_broadcast(handle: i64) -> (i64, i64) {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    match socket.broadcast() {
        Ok(broadcast) => (if broadcast { 1 } else { 0 }, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Get TTL.
/// Returns (ttl, error_code)
#[no_mangle]
pub extern "C" fn native_udp_get_ttl(handle: i64) -> (i64, i64) {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return (0, NetError::InvalidHandle as i64),
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return (0, NetError::InvalidHandle as i64),
    };

    match socket.ttl() {
        Ok(ttl) => (ttl as i64, NetError::Success as i64),
        Err(e) => (0, NetError::from(e) as i64),
    }
}

/// Join IPv4 multicast group.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_join_multicast_v4(handle: i64, multiaddr: i64, interface: i64) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    // multiaddr and interface are packed as u32 IPv4 addresses
    let multi = Ipv4Addr::from((multiaddr as u32).to_be_bytes());
    let iface = Ipv4Addr::from((interface as u32).to_be_bytes());

    match socket.join_multicast_v4(&multi, &iface) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Leave IPv4 multicast group.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_leave_multicast_v4(
    handle: i64,
    multiaddr: i64,
    interface: i64,
) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    let multi = Ipv4Addr::from((multiaddr as u32).to_be_bytes());
    let iface = Ipv4Addr::from((interface as u32).to_be_bytes());

    match socket.leave_multicast_v4(&multi, &iface) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Join IPv6 multicast group.
/// Returns error_code
#[no_mangle]
pub unsafe extern "C" fn native_udp_join_multicast_v6(
    handle: i64,
    multiaddr_ptr: i64,
    interface: i64,
) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    // multiaddr_ptr points to 16 bytes of IPv6 address
    if multiaddr_ptr == 0 {
        return NetError::InvalidInput as i64;
    }
    let bytes = std::slice::from_raw_parts(multiaddr_ptr as *const u8, 16);
    let mut arr = [0u8; 16];
    arr.copy_from_slice(bytes);
    let multi = Ipv6Addr::from(arr);

    match socket.join_multicast_v6(&multi, interface as u32) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Leave IPv6 multicast group.
/// Returns error_code
#[no_mangle]
pub unsafe extern "C" fn native_udp_leave_multicast_v6(
    handle: i64,
    multiaddr_ptr: i64,
    interface: i64,
) -> i64 {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let entry = match registry.get(&handle) {
        Some(e) => e,
        None => return NetError::InvalidHandle as i64,
    };

    let socket = match entry {
        SocketEntry::UdpSocket(s) => s,
        _ => return NetError::InvalidHandle as i64,
    };

    if multiaddr_ptr == 0 {
        return NetError::InvalidInput as i64;
    }
    let bytes = std::slice::from_raw_parts(multiaddr_ptr as *const u8, 16);
    let mut arr = [0u8; 16];
    arr.copy_from_slice(bytes);
    let multi = Ipv6Addr::from(arr);

    match socket.leave_multicast_v6(&multi, interface as u32) {
        Ok(_) => NetError::Success as i64,
        Err(e) => NetError::from(e) as i64,
    }
}

/// Close a UDP socket.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_close(handle: i64) -> i64 {
    match unregister_socket(handle) {
        Some(_) => NetError::Success as i64,
        None => NetError::InvalidHandle as i64,
    }
}

// ============================================================================
// HTTP FFI functions
// ============================================================================

/// HTTP request structure passed from Simple code
/// This is a simplified representation - the actual parsing happens in this function
#[repr(C)]
pub struct HttpRequestData {
    pub method: i64,       // 0=GET, 1=POST, 2=PUT, 3=DELETE, 4=PATCH, 5=HEAD
    pub url_ptr: i64,      // Pointer to URL string
    pub url_len: i64,      // Length of URL string
    pub body_ptr: i64,     // Pointer to body bytes (0 if no body)
    pub body_len: i64,     // Length of body
    pub headers_ptr: i64,  // Pointer to headers array
    pub headers_count: i64, // Number of header pairs
}

/// Send an HTTP request.
/// Returns (response_ptr, error_code)
/// Response is a RuntimeValue containing the response data
#[no_mangle]
pub unsafe extern "C" fn native_http_send(request_ptr: i64, timeout_ns: i64) -> (i64, i64) {
    // Parse the URL from the request
    if request_ptr == 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let req_data = &*(request_ptr as *const HttpRequestData);

    // Parse URL
    if req_data.url_ptr == 0 || req_data.url_len <= 0 {
        return (0, NetError::HttpInvalidUrl as i64);
    }
    let url_slice =
        std::slice::from_raw_parts(req_data.url_ptr as *const u8, req_data.url_len as usize);
    let url_str = match std::str::from_utf8(url_slice) {
        Ok(s) => s,
        Err(_) => return (0, NetError::HttpInvalidUrl as i64),
    };

    // Build the request
    let method = match req_data.method {
        0 => "GET",
        1 => "POST",
        2 => "PUT",
        3 => "DELETE",
        4 => "PATCH",
        5 => "HEAD",
        _ => "GET",
    };

    // Create the request builder
    let mut request = ureq::request(method, url_str);

    // Set timeout if specified
    if timeout_ns > 0 {
        let timeout = Duration::from_nanos(timeout_ns as u64);
        request = request.timeout(timeout);
    }

    // Add body if present
    let response = if req_data.body_ptr != 0 && req_data.body_len > 0 {
        let body =
            std::slice::from_raw_parts(req_data.body_ptr as *const u8, req_data.body_len as usize);
        request.send_bytes(body)
    } else {
        request.call()
    };

    match response {
        Ok(resp) => {
            // Read response body
            let status = resp.status();
            let body = match resp.into_string() {
                Ok(s) => s,
                Err(_) => return (0, NetError::HttpInvalidResponse as i64),
            };

            // Allocate response structure
            // Format: status (i64) + body_len (i64) + body_ptr (i64)
            let body_bytes = body.into_bytes();
            let body_len = body_bytes.len();
            let body_box = body_bytes.into_boxed_slice();
            let body_ptr = Box::into_raw(body_box) as *const u8 as i64;

            // Allocate response header: [status, body_len, body_ptr]
            let response_data = Box::new([status as i64, body_len as i64, body_ptr]);
            let response_ptr = Box::into_raw(response_data) as i64;

            (response_ptr, NetError::Success as i64)
        }
        Err(e) => {
            let error_code = match e {
                ureq::Error::Status(code, _) => {
                    // HTTP error status - still return as success with status code
                    // The caller can check the status code
                    if code >= 400 {
                        NetError::HttpError as i64
                    } else {
                        NetError::Success as i64
                    }
                }
                ureq::Error::Transport(transport) => {
                    use ureq::ErrorKind::*;
                    match transport.kind() {
                        InvalidUrl => NetError::HttpInvalidUrl as i64,
                        Dns | ConnectionFailed => NetError::ConnectionRefused as i64,
                        TooManyRedirects => NetError::HttpTooManyRedirects as i64,
                        Io => NetError::Unknown as i64,
                        _ => NetError::HttpError as i64,
                    }
                }
            };
            (0, error_code)
        }
    }
}

/// Free an HTTP response allocated by native_http_send.
#[no_mangle]
pub unsafe extern "C" fn native_http_response_free(response_ptr: i64) {
    if response_ptr == 0 {
        return;
    }

    // Response format: [status, body_len, body_ptr]
    let response_data = Box::from_raw(response_ptr as *mut [i64; 3]);
    let body_ptr = response_data[2];
    let body_len = response_data[1] as usize;

    if body_ptr != 0 && body_len > 0 {
        // Free the body
        let body = std::slice::from_raw_parts_mut(body_ptr as *mut u8, body_len);
        let _ = Box::from_raw(body as *mut [u8]);
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_socket_registry_basic() {
        // Create a UDP socket to test registry
        let socket = UdpSocket::bind("127.0.0.1:0").unwrap();
        let handle = register_udp_socket(socket);
        assert!(handle > 0);

        // Verify it's in the registry
        {
            let registry = SOCKET_REGISTRY.lock().unwrap();
            assert!(registry.contains_key(&handle));
        }

        // Remove it
        let removed = unregister_socket(handle);
        assert!(removed.is_some());

        // Verify it's gone
        {
            let registry = SOCKET_REGISTRY.lock().unwrap();
            assert!(!registry.contains_key(&handle));
        }
    }

    #[test]
    fn test_error_conversion() {
        use std::io::{Error, ErrorKind};

        assert_eq!(NetError::from(Error::from(ErrorKind::AddrInUse)), NetError::AddrInUse);
        assert_eq!(NetError::from(Error::from(ErrorKind::ConnectionRefused)), NetError::ConnectionRefused);
        assert_eq!(NetError::from(Error::from(ErrorKind::TimedOut)), NetError::TimedOut);
    }

    #[test]
    fn test_parse_socket_addr_ipv4() {
        let addr_str = "127.0.0.1:8080";
        unsafe {
            let result = parse_socket_addr(addr_str.as_ptr() as i64, addr_str.len() as i64);
            assert!(result.is_ok());
            let addr = result.unwrap();
            assert_eq!(addr.port(), 8080);
        }
    }

    #[test]
    fn test_parse_socket_addr_ipv6() {
        let addr_str = "[::1]:9000";
        unsafe {
            let result = parse_socket_addr(addr_str.as_ptr() as i64, addr_str.len() as i64);
            assert!(result.is_ok());
            let addr = result.unwrap();
            assert_eq!(addr.port(), 9000);
        }
    }

    #[test]
    fn test_tcp_bind_and_close() {
        let addr = "127.0.0.1:0";
        unsafe {
            let (handle, err) = native_tcp_bind(addr.as_ptr() as i64, addr.len() as i64);
            assert_eq!(err, NetError::Success as i64);
            assert!(handle > 0);

            let close_err = native_tcp_close(handle);
            assert_eq!(close_err, NetError::Success as i64);
        }
    }

    #[test]
    fn test_udp_bind_and_close() {
        let addr = "127.0.0.1:0";
        unsafe {
            let (handle, err) = native_udp_bind(addr.as_ptr() as i64, addr.len() as i64);
            assert_eq!(err, NetError::Success as i64);
            assert!(handle > 0);

            let close_err = native_udp_close(handle);
            assert_eq!(close_err, NetError::Success as i64);
        }
    }

    #[test]
    fn test_invalid_handle() {
        let result = native_tcp_close(99999);
        assert_eq!(result, NetError::InvalidHandle as i64);

        let result = native_udp_close(99999);
        assert_eq!(result, NetError::InvalidHandle as i64);
    }
}
