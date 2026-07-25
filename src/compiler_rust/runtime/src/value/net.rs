//! Networking SFFI functions for TCP, UDP, and HTTP.
//!
//! This module provides the native implementations for the Simple language's
//! networking APIs. Sockets are managed via numeric handles stored in a
//! global registry.

use lazy_static::lazy_static;
use socket2::{Domain, Protocol, Socket, Type};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, TcpListener, TcpStream, ToSocketAddrs, UdpSocket};
#[cfg(unix)]
use std::os::unix::io::AsRawFd;
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
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
    TcpSocket(Socket),
    TcpListener(TcpListener),
    TcpStream(TcpStream),
    UdpSocket(UdpSocket),
}

lazy_static! {
    /// Global socket registry mapping handles to socket objects
    static ref SOCKET_REGISTRY: Mutex<HashMap<i64, SocketEntry>> = Mutex::new(HashMap::new());
    /// Counter for generating unique handles
    static ref NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);
    static ref EVENT_LOOP_REGISTRY: Mutex<HashMap<i64, Vec<(i64, i64)>>> = Mutex::new(HashMap::new());
    static ref EVENT_LOOP_POLL_RESULTS: Mutex<Vec<i64>> = Mutex::new(Vec::new());
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
/// Returns a pointer to the string (caller must free via `rt_net_free_addr_string`)
fn addr_to_string_ptr(addr: &SocketAddr) -> i64 {
    let s = addr.to_string();
    let boxed = s.into_boxed_str();
    Box::into_raw(boxed) as *const str as *const u8 as i64
}

/// Free a string previously allocated by `addr_to_string_ptr`.
///
/// # Safety
/// `ptr` must be a value returned by a network function that allocates address strings,
/// and `len` must be the length of that string.
#[no_mangle]
pub extern "C" fn rt_net_free_addr_string(ptr: i64, len: i64) {
    if ptr == 0 || len <= 0 {
        return;
    }
    unsafe {
        let slice_ptr = std::ptr::slice_from_raw_parts_mut(ptr as *mut u8, len as usize);
        let _ = Box::from_raw(slice_ptr as *mut str);
    }
}

// ============================================================================
// Helper macros for reducing SFFI boilerplate
// ============================================================================

/// Macro to get registry and socket entry with error handling
/// Usage: with_socket!(handle, UdpSocket, error_fn, socket => { use socket here })
macro_rules! with_socket {
    ($handle:expr, $variant:ident, $error_ret:expr, $socket:ident => $body:expr) => {{
        let registry = SOCKET_REGISTRY.lock().unwrap();
        let entry = match registry.get(&$handle) {
            Some(e) => e,
            None => return $error_ret(NetError::InvalidHandle),
        };
        let $socket = match entry {
            SocketEntry::$variant(s) => s,
            _ => return $error_ret(NetError::InvalidHandle),
        };
        $body
    }};
}

/// Macro to get mutable registry and socket entry with error handling
/// Usage: with_socket_mut!(handle, TcpStream, error_fn, socket => { use socket here })
macro_rules! with_socket_mut {
    ($handle:expr, $variant:ident, $error_ret:expr, $socket:ident => $body:expr) => {{
        let mut registry = SOCKET_REGISTRY.lock().unwrap();
        let entry = match registry.get_mut(&$handle) {
            Some(e) => e,
            None => return $error_ret(NetError::InvalidHandle),
        };
        let $socket = match entry {
            SocketEntry::$variant(s) => s,
            _ => return $error_ret(NetError::InvalidHandle),
        };
        $body
    }};
}

/// Macro to validate buffer pointer and length
/// Returns early with InvalidInput error if validation fails
macro_rules! validate_buffer {
    ($buf_ptr:expr, $buf_len:expr, $error_ret:expr) => {
        if $buf_ptr == 0 || $buf_len <= 0 {
            return $error_ret(NetError::InvalidInput);
        }
    };
}

/// Macro to parse socket address from SFFI parameters
/// Returns early with error if parsing fails
macro_rules! parse_addr {
    ($addr_ptr:expr, $addr_len:expr, $error_ret:expr) => {{
        match parse_socket_addr($addr_ptr, $addr_len) {
            Ok(a) => a,
            Err(e) => return $error_ret(e),
        }
    }};
}

/// Convert error code to i64
#[inline]
fn err_to_i64(e: NetError) -> i64 {
    e as i64
}

/// Convert error code to (0, error_code) tuple
#[inline]
fn err_to_tuple2(e: NetError) -> (i64, i64) {
    (0, e as i64)
}

/// Convert error code to (0, 0, error_code) tuple
#[inline]
fn err_to_tuple3(e: NetError) -> (i64, i64, i64) {
    (0, 0, e as i64)
}

/// Helper trait for sockets that support timeout configuration
trait TimeoutSocket {
    fn set_read_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()>;
    fn set_write_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()>;
}

impl TimeoutSocket for UdpSocket {
    fn set_read_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        UdpSocket::set_read_timeout(self, timeout)
    }
    fn set_write_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        UdpSocket::set_write_timeout(self, timeout)
    }
}

impl TimeoutSocket for TcpStream {
    fn set_read_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        TcpStream::set_read_timeout(self, timeout)
    }
    fn set_write_timeout(&self, timeout: Option<Duration>) -> std::io::Result<()> {
        TcpStream::set_write_timeout(self, timeout)
    }
}

/// Unified close function for all socket types
fn close_socket(handle: i64) -> i64 {
    match unregister_socket(handle) {
        Some(_) => NetError::Success as i64,
        None => NetError::InvalidHandle as i64,
    }
}

/// Macro to create timeout setter functions (read/write)
/// Usage: impl_timeout_setters!(native_tcp_set_read_timeout, TcpStream, read)
macro_rules! impl_timeout_setter {
    ($fn_name:ident, $socket_type:ident, $timeout_method:ident) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(handle: i64, timeout_ns: i64) -> i64 {
            with_socket!(handle, $socket_type, err_to_i64, socket => {
                let timeout = if timeout_ns > 0 {
                    Some(Duration::from_nanos(timeout_ns as u64))
                } else {
                    None
                };

                match socket.$timeout_method(timeout) {
                    Ok(_) => NetError::Success as i64,
                    Err(e) => NetError::from(e) as i64,
                }
            })
        }
    };
}

// ============================================================================
// TCP SFFI functions (extracted to net_tcp.rs)
// ============================================================================
include!("net_tcp.rs");

// ============================================================================
// TLS transport SFFI shims (extracted to net_tls.rs)
// ============================================================================
#[cfg(feature = "runtime-tls")]
include!("net_tls.rs");
#[cfg(not(feature = "runtime-tls"))]
include!("net_tls_stub.rs");

// ============================================================================
// UDP SFFI functions (extracted to net_udp.rs)
// ============================================================================
include!("net_udp.rs");

// ============================================================================
// HTTP SFFI functions (extracted to net_http.rs)
// ============================================================================
#[cfg(feature = "runtime-http")]
include!("net_http.rs");
#[cfg(not(feature = "runtime-http"))]
include!("net_http_stub.rs");

// ============================================================================
// Unix-domain socket SFFI functions (extracted to net_uds.rs)
// Added 2026-04-26 for jj-wrapper-daemon (D-4 / SJ-UDS-001)
// ============================================================================
#[cfg(unix)]
include!("net_uds.rs");

#[cfg(windows)]
mod net_uds_windows {
    const NEG_ENOSYS: i64 = -38;
    const NEG_EINVAL: i64 = -22;

    #[no_mangle]
    pub unsafe extern "C" fn rt_unix_socket_listen(_path_ptr: i64, _path_len: i64, _backlog: i32) -> i64 {
        NEG_ENOSYS
    }

    #[no_mangle]
    pub extern "C" fn rt_unix_socket_accept(_fd: i64) -> i64 {
        NEG_ENOSYS
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_unix_socket_send(_fd: i64, data_ptr: i64, data_len: i64) -> i64 {
        if data_ptr == 0 || data_len < 0 {
            return NEG_EINVAL;
        }
        NEG_ENOSYS
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_unix_socket_recv(_fd: i64, _max_len: i64, out_len: *mut i64) -> i64 {
        if !out_len.is_null() {
            *out_len = NEG_ENOSYS;
        }
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_unix_socket_free_buf(_ptr: i64, _len: i64) {}

    #[no_mangle]
    pub extern "C" fn rt_unix_socket_close(_fd: i64) -> i32 {
        NEG_ENOSYS as i32
    }

    #[no_mangle]
    pub unsafe extern "C" fn rt_unix_socket_connect(_path_ptr: i64, _path_len: i64) -> i64 {
        NEG_ENOSYS
    }
}

/// Register a pre-bind TCP socket and return its handle
fn register_tcp_socket(socket: Socket) -> i64 {
    let handle = alloc_handle();
    SOCKET_REGISTRY
        .lock()
        .unwrap()
        .insert(handle, SocketEntry::TcpSocket(socket));
    handle
}

#[no_mangle]
pub extern "C" fn rt_event_loop_create() -> i64 {
    let handle = alloc_handle();
    EVENT_LOOP_REGISTRY.lock().unwrap().insert(handle, Vec::new());
    handle
}

#[no_mangle]
pub extern "C" fn rt_event_loop_register(loop_fd: i64, fd: i64, _interest: i64, _token: i64, _edge: bool) -> bool {
    let mut registry = EVENT_LOOP_REGISTRY.lock().unwrap();
    let Some(entries) = registry.get_mut(&loop_fd) else {
        return false;
    };
    if let Some(existing) = entries.iter_mut().find(|(candidate, _)| *candidate == fd) {
        existing.1 = _interest;
    } else {
        entries.push((fd, _interest));
    }
    true
}

#[no_mangle]
pub extern "C" fn rt_event_loop_deregister(loop_fd: i64, fd: i64) -> bool {
    let mut registry = EVENT_LOOP_REGISTRY.lock().unwrap();
    let Some(entries) = registry.get_mut(&loop_fd) else {
        return false;
    };
    entries.retain(|(candidate, _)| *candidate != fd);
    true
}

#[no_mangle]
pub extern "C" fn rt_event_loop_poll(loop_fd: i64, max_events: i64, timeout_ms: i64) -> i64 {
    EVENT_LOOP_POLL_RESULTS.lock().unwrap().clear();

    #[cfg(unix)]
    {
        let entries = {
            let registry = EVENT_LOOP_REGISTRY.lock().unwrap();
            match registry.get(&loop_fd) {
                Some(entries) => entries.clone(),
                None => return 0,
            }
        };
        if entries.is_empty() || max_events <= 0 {
            return 0;
        }

        let socket_registry = SOCKET_REGISTRY.lock().unwrap();
        let mut poll_fds: Vec<(i64, libc::pollfd)> = Vec::new();
        for (handle, interest) in entries {
            let Some(entry) = socket_registry.get(&handle) else {
                continue;
            };
            let raw_fd = match entry {
                SocketEntry::TcpSocket(socket) => socket.as_raw_fd(),
                SocketEntry::TcpListener(listener) => listener.as_raw_fd(),
                SocketEntry::TcpStream(stream) => stream.as_raw_fd(),
                SocketEntry::UdpSocket(socket) => socket.as_raw_fd(),
            };
            let events = match interest {
                1 => libc::POLLOUT | libc::POLLERR | libc::POLLHUP,
                2 => libc::POLLIN | libc::POLLOUT | libc::POLLERR | libc::POLLHUP,
                _ => libc::POLLIN | libc::POLLERR | libc::POLLHUP,
            };
            poll_fds.push((
                handle,
                libc::pollfd {
                    fd: raw_fd,
                    events,
                    revents: 0,
                },
            ));
        }
        drop(socket_registry);

        if poll_fds.is_empty() {
            return 0;
        }
        let timeout = timeout_ms.clamp(-1, i32::MAX as i64) as libc::c_int;
        let rc = unsafe {
            libc::poll(
                poll_fds.as_mut_ptr() as *mut libc::pollfd,
                poll_fds.len() as libc::nfds_t,
                timeout,
            )
        };
        if rc <= 0 {
            return 0;
        }

        let mut results = EVENT_LOOP_POLL_RESULTS.lock().unwrap();
        let limit = max_events.min(256) as usize;
        for (handle, poll_fd) in poll_fds {
            if poll_fd.revents != 0 {
                results.push(handle);
                if results.len() >= limit {
                    break;
                }
            }
        }
        results.len() as i64
    }

    #[cfg(not(unix))]
    {
        let _ = loop_fd;
        let _ = max_events;
        let _ = timeout_ms;
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_event_loop_poll_get_fd(index: i64) -> i64 {
    if index < 0 {
        return -1;
    }
    EVENT_LOOP_POLL_RESULTS
        .lock()
        .unwrap()
        .get(index as usize)
        .copied()
        .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn rt_event_loop_close(loop_fd: i64) -> bool {
    EVENT_LOOP_REGISTRY.lock().unwrap().remove(&loop_fd).is_some()
}

// ============================================================================
// Registry Cleanup (for test isolation)
// ============================================================================

/// Clear all socket handles (for test cleanup)
/// Note: This closes all open sockets
pub fn clear_socket_registry() {
    SOCKET_REGISTRY.lock().unwrap().clear();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_string_data, rt_string_len};

    unsafe fn runtime_string(value: crate::value::RuntimeValue) -> String {
        assert!(!value.is_nil());
        let len = rt_string_len(value);
        let ptr = rt_string_data(value);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

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
        assert_eq!(
            NetError::from(Error::from(ErrorKind::ConnectionRefused)),
            NetError::ConnectionRefused
        );
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
    fn test_tcp_read_line_consumes_only_through_newline() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let client = std::thread::spawn(move || {
            let mut stream = TcpStream::connect(addr).unwrap();
            stream.write_all(b"GET / HTTP/1.1\r\nHost: example\r\n\r\n").unwrap();
        });

        let (stream, _) = listener.accept().unwrap();
        let handle = register_tcp_stream(stream);

        unsafe {
            assert_eq!(runtime_string(rt_io_tcp_read_line(handle)), "GET / HTTP/1.1\r\n");
            assert_eq!(runtime_string(rt_io_tcp_read_line(handle)), "Host: example\r\n");
        }

        assert_eq!(native_tcp_close(handle), NetError::Success as i64);
        client.join().unwrap();
    }

    #[test]
    fn test_tcp_drain_line_consumes_without_allocating_text() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let client = std::thread::spawn(move || {
            let mut stream = TcpStream::connect(addr).unwrap();
            stream.write_all(b"GET / HTTP/1.1\r\nHost: example\r\n\r\n").unwrap();
        });

        let (stream, _) = listener.accept().unwrap();
        let handle = register_tcp_stream(stream);

        assert_eq!(rt_io_tcp_drain_line(handle), 16);
        unsafe {
            assert_eq!(runtime_string(rt_io_tcp_read_line(handle)), "Host: example\r\n");
        }

        assert_eq!(native_tcp_close(handle), NetError::Success as i64);
        client.join().unwrap();
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
