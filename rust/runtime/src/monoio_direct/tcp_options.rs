// TCP socket options for direct monoio I/O
// Feature: monoio-direct

use crate::monoio_runtime::direct::with_registry;
use crate::value::RuntimeValue;

// ============================================================================
// TCP Socket Options
// ============================================================================

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
