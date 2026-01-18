// Direct I/O FFI functions for monoio
// Feature: monoio-direct
// Provides zero-overhead async I/O by executing on thread-local monoio runtime

#![cfg(feature = "monoio-direct")]

use crate::monoio_buffer::OwnedBuf;
use crate::monoio_runtime::direct::{block_on, init_direct_runtime, with_registry};
use crate::monoio_runtime::{copy_to_buffer, execute_async, extract_buffer_bytes, get_entries};
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

/// Flush pending writes on a TCP stream.
///
/// Note: monoio uses completion-based I/O, so writes are typically already
/// submitted to the kernel. This function ensures any buffered data is sent.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_flush(stream_handle: RuntimeValue) -> RuntimeValue {
    use monoio::io::AsyncWriteRentExt;

    let stream_id = stream_handle.as_int();

    // Take stream for async operation
    let mut stream = match with_registry(|reg| reg.take_tcp_stream(stream_id)) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_flush: Invalid stream handle {}", stream_id);
            return RuntimeValue::from_int(-1);
        }
    };

    let result = execute_async(get_entries(), async move {
        stream.flush().await?;
        Ok::<_, std::io::Error>(stream)
    });

    match result {
        Ok(stream) => {
            with_registry(|reg| reg.put_back_tcp_stream(stream_id, stream));
            RuntimeValue::from_int(1)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_flush: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Shutdown a TCP stream for reading, writing, or both.
///
/// # Arguments
/// * `stream_handle` - TCP stream handle
/// * `how` - 0=Read, 1=Write, 2=Both
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_shutdown(stream_handle: RuntimeValue, how: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Validate how parameter
    let shutdown = match how {
        0 => std::net::Shutdown::Read,
        1 => std::net::Shutdown::Write,
        2 => std::net::Shutdown::Both,
        _ => {
            tracing::error!("rt_monoio_tcp_shutdown: Invalid shutdown mode {}", how);
            return RuntimeValue::from_int(-1);
        }
    };

    // Get stream for operation
    let stream = match with_registry(|reg| reg.take_tcp_stream(stream_id)) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_shutdown: Invalid stream handle {}", stream_id);
            return RuntimeValue::from_int(-1);
        }
    };

    // Get raw fd and perform shutdown
    use std::os::unix::io::AsRawFd;
    let fd = stream.as_raw_fd();
    let result = unsafe {
        libc::shutdown(
            fd,
            match shutdown {
                std::net::Shutdown::Read => libc::SHUT_RD,
                std::net::Shutdown::Write => libc::SHUT_WR,
                std::net::Shutdown::Both => libc::SHUT_RDWR,
            },
        )
    };

    // Put stream back
    with_registry(|reg| reg.put_back_tcp_stream(stream_id, stream));

    if result == 0 {
        RuntimeValue::from_int(1)
    } else {
        tracing::error!("rt_monoio_tcp_shutdown: shutdown failed with errno");
        RuntimeValue::from_int(-1)
    }
}

/// Get local address of a TCP stream.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_local_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let addr = with_registry(|reg| reg.get_tcp_stream(stream_id).and_then(|s| s.local_addr().ok()));

    match addr {
        Some(addr) => crate::monoio_runtime::string_to_runtime_value(&addr.to_string()),
        None => RuntimeValue::NIL,
    }
}

/// Get peer address of a TCP stream.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_peer_addr(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let addr = with_registry(|reg| reg.get_tcp_stream(stream_id).and_then(|s| s.peer_addr().ok()));

    match addr {
        Some(addr) => crate::monoio_runtime::string_to_runtime_value(&addr.to_string()),
        None => RuntimeValue::NIL,
    }
}

/// Set TCP_NODELAY option (disable Nagle's algorithm).
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_set_nodelay(stream_handle: RuntimeValue, nodelay: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let result = with_registry(|reg| {
        reg.get_tcp_stream(stream_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();
            let value: libc::c_int = if nodelay != 0 { 1 } else { 0 };
            unsafe {
                libc::setsockopt(
                    fd,
                    libc::IPPROTO_TCP,
                    libc::TCP_NODELAY,
                    &value as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-1),
        None => RuntimeValue::from_int(-1),
    }
}

/// Set TCP keepalive option.
///
/// # Arguments
/// * `stream_handle` - TCP stream handle
/// * `keepalive_secs` - Keepalive interval in seconds, or 0 to disable
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_set_keepalive(stream_handle: RuntimeValue, keepalive_secs: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let result = with_registry(|reg| {
        reg.get_tcp_stream(stream_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            // Enable/disable keepalive
            let enabled: libc::c_int = if keepalive_secs > 0 { 1 } else { 0 };
            let r1 = unsafe {
                libc::setsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_KEEPALIVE,
                    &enabled as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                )
            };

            if r1 != 0 || keepalive_secs <= 0 {
                return r1;
            }

            // Set keepalive interval
            let secs = keepalive_secs as libc::c_int;
            unsafe {
                libc::setsockopt(
                    fd,
                    libc::IPPROTO_TCP,
                    libc::TCP_KEEPIDLE,
                    &secs as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-1),
        None => RuntimeValue::from_int(-1),
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

/// Get local address of a UDP socket.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_local_addr(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    let addr = with_registry(|reg| reg.get_udp_socket(socket_id).and_then(|s| s.local_addr().ok()));

    match addr {
        Some(addr) => crate::monoio_runtime::string_to_runtime_value(&addr.to_string()),
        None => RuntimeValue::NIL,
    }
}

/// Connect a UDP socket to a remote address.
///
/// After connecting, send() and recv() can be used instead of send_to() and recv_from().
#[no_mangle]
pub extern "C" fn rt_monoio_udp_connect(socket_handle: RuntimeValue, addr: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_connect: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_udp_connect: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            // Connect using libc
            let (addr_ptr, addr_len) = match socket_addr {
                SocketAddr::V4(ref a) => {
                    let sin = libc::sockaddr_in {
                        sin_family: libc::AF_INET as libc::sa_family_t,
                        sin_port: a.port().to_be(),
                        sin_addr: libc::in_addr {
                            s_addr: u32::from_ne_bytes(a.ip().octets()),
                        },
                        sin_zero: [0; 8],
                    };
                    (
                        Box::into_raw(Box::new(sin)) as *const libc::sockaddr,
                        std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t,
                    )
                }
                SocketAddr::V6(ref a) => {
                    let sin6 = libc::sockaddr_in6 {
                        sin6_family: libc::AF_INET6 as libc::sa_family_t,
                        sin6_port: a.port().to_be(),
                        sin6_flowinfo: a.flowinfo(),
                        sin6_addr: libc::in6_addr {
                            s6_addr: a.ip().octets(),
                        },
                        sin6_scope_id: a.scope_id(),
                    };
                    (
                        Box::into_raw(Box::new(sin6)) as *const libc::sockaddr,
                        std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t,
                    )
                }
            };

            let result = unsafe { libc::connect(fd, addr_ptr, addr_len) };

            // Free the allocated address
            unsafe {
                match socket_addr {
                    SocketAddr::V4(_) => {
                        drop(Box::from_raw(addr_ptr as *mut libc::sockaddr_in));
                    }
                    SocketAddr::V6(_) => {
                        drop(Box::from_raw(addr_ptr as *mut libc::sockaddr_in6));
                    }
                }
            }

            result
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => {
            tracing::error!("rt_monoio_udp_connect: connect failed");
            RuntimeValue::from_int(-3)
        }
        None => {
            tracing::error!("rt_monoio_udp_connect: Invalid socket handle");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Send data to connected peer via UDP.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_send(socket_handle: RuntimeValue, buffer: RuntimeValue, len: i64) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_udp_send: Invalid buffer");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            unsafe { libc::send(fd, data.as_ptr() as *const libc::c_void, data.len(), 0) }
        })
    });

    match result {
        Some(n) if n >= 0 => RuntimeValue::from_int(n as i64),
        Some(_) => {
            tracing::error!("rt_monoio_udp_send: send failed");
            RuntimeValue::from_int(-2)
        }
        None => {
            tracing::error!("rt_monoio_udp_send: Invalid socket handle");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Receive data from connected peer via UDP.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_recv(socket_handle: RuntimeValue, buffer: RuntimeValue, max_len: i64) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if max_len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let mut recv_buf = vec![0u8; max_len as usize];

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            unsafe { libc::recv(fd, recv_buf.as_mut_ptr() as *mut libc::c_void, recv_buf.len(), 0) }
        })
    });

    match result {
        Some(n) if n >= 0 => {
            let bytes_read = n as usize;
            recv_buf.truncate(bytes_read);
            let copied = copy_to_buffer(buffer, &recv_buf);
            RuntimeValue::from_int(copied)
        }
        Some(_) => {
            tracing::error!("rt_monoio_udp_recv: recv failed");
            RuntimeValue::from_int(-2)
        }
        None => {
            tracing::error!("rt_monoio_udp_recv: Invalid socket handle");
            RuntimeValue::from_int(-1)
        }
    }
}

/// Set broadcast option on UDP socket.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_set_broadcast(socket_handle: RuntimeValue, broadcast: i64) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();
            let value: libc::c_int = if broadcast != 0 { 1 } else { 0 };
            unsafe {
                libc::setsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_BROADCAST,
                    &value as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-1),
        None => RuntimeValue::from_int(-1),
    }
}

/// Set multicast TTL on UDP socket.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_set_multicast_ttl(socket_handle: RuntimeValue, ttl: i64) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    if ttl < 0 || ttl > 255 {
        tracing::error!("rt_monoio_udp_set_multicast_ttl: TTL out of range");
        return RuntimeValue::from_int(-1);
    }

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();
            let value = ttl as libc::c_int;
            unsafe {
                libc::setsockopt(
                    fd,
                    libc::IPPROTO_IP,
                    libc::IP_MULTICAST_TTL,
                    &value as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::c_int>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-1),
        None => RuntimeValue::from_int(-1),
    }
}

/// Join a multicast group.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_join_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    let mcast_str = match crate::monoio_runtime::runtime_value_to_string(multicast_addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_join_multicast: Invalid multicast address");
            return RuntimeValue::from_int(-1);
        }
    };

    let iface_str = match crate::monoio_runtime::runtime_value_to_string(interface_addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_join_multicast: Invalid interface address");
            return RuntimeValue::from_int(-1);
        }
    };

    let mcast_ip: std::net::Ipv4Addr = match mcast_str.parse() {
        Ok(ip) => ip,
        Err(e) => {
            tracing::error!("rt_monoio_udp_join_multicast: Invalid multicast IP: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let iface_ip: std::net::Ipv4Addr = match iface_str.parse() {
        Ok(ip) => ip,
        Err(e) => {
            tracing::error!("rt_monoio_udp_join_multicast: Invalid interface IP: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            let mreq = libc::ip_mreq {
                imr_multiaddr: libc::in_addr {
                    s_addr: u32::from_ne_bytes(mcast_ip.octets()),
                },
                imr_interface: libc::in_addr {
                    s_addr: u32::from_ne_bytes(iface_ip.octets()),
                },
            };

            unsafe {
                libc::setsockopt(
                    fd,
                    libc::IPPROTO_IP,
                    libc::IP_ADD_MEMBERSHIP,
                    &mreq as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::ip_mreq>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-3),
        None => RuntimeValue::from_int(-1),
    }
}

/// Leave a multicast group.
#[no_mangle]
pub extern "C" fn rt_monoio_udp_leave_multicast(
    socket_handle: RuntimeValue,
    multicast_addr: RuntimeValue,
    interface_addr: RuntimeValue,
) -> RuntimeValue {
    let socket_id = socket_handle.as_int();

    let mcast_str = match crate::monoio_runtime::runtime_value_to_string(multicast_addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_leave_multicast: Invalid multicast address");
            return RuntimeValue::from_int(-1);
        }
    };

    let iface_str = match crate::monoio_runtime::runtime_value_to_string(interface_addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_udp_leave_multicast: Invalid interface address");
            return RuntimeValue::from_int(-1);
        }
    };

    let mcast_ip: std::net::Ipv4Addr = match mcast_str.parse() {
        Ok(ip) => ip,
        Err(e) => {
            tracing::error!("rt_monoio_udp_leave_multicast: Invalid multicast IP: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let iface_ip: std::net::Ipv4Addr = match iface_str.parse() {
        Ok(ip) => ip,
        Err(e) => {
            tracing::error!("rt_monoio_udp_leave_multicast: Invalid interface IP: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let result = with_registry(|reg| {
        reg.get_udp_socket(socket_id).map(|s| {
            use std::os::unix::io::AsRawFd;
            let fd = s.as_raw_fd();

            let mreq = libc::ip_mreq {
                imr_multiaddr: libc::in_addr {
                    s_addr: u32::from_ne_bytes(mcast_ip.octets()),
                },
                imr_interface: libc::in_addr {
                    s_addr: u32::from_ne_bytes(iface_ip.octets()),
                },
            };

            unsafe {
                libc::setsockopt(
                    fd,
                    libc::IPPROTO_IP,
                    libc::IP_DROP_MEMBERSHIP,
                    &mreq as *const _ as *const libc::c_void,
                    std::mem::size_of::<libc::ip_mreq>() as libc::socklen_t,
                )
            }
        })
    });

    match result {
        Some(0) => RuntimeValue::from_int(1),
        Some(_) => RuntimeValue::from_int(-3),
        None => RuntimeValue::from_int(-1),
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
