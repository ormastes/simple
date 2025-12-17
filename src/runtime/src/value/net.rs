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
// TCP FFI functions (extracted to net_tcp.rs)
// ============================================================================
include!("net_tcp.rs");

// ============================================================================
// UDP FFI functions (extracted to net_udp.rs)
// ============================================================================
include!("net_udp.rs");

// ============================================================================
// HTTP FFI functions (extracted to net_http.rs)
// ============================================================================
include!("net_http.rs");

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
