// Core UDP operations for direct monoio I/O
// Feature: monoio-direct

use crate::monoio_buffer::OwnedBuf;
use crate::monoio_runtime::direct::{block_on, with_registry};
use crate::monoio_runtime::{copy_to_buffer, extract_buffer_bytes};
use crate::value::RuntimeValue;
use monoio::net::udp::UdpSocket;
use std::net::SocketAddr;

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
