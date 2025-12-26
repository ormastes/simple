// ============================================================================
// TCP FFI functions
// ============================================================================

/// Bind a TCP listener to an address.
/// Returns (handle, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64) {
    let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple2);

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
    let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple3);

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
    let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple3);

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
    validate_buffer!(buf_ptr, buf_len, err_to_tuple2);

    with_socket_mut!(handle, TcpStream, err_to_tuple2, stream => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match stream.read(buf) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Write data to a TCP stream.
/// Returns (bytes_written, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_write(
    handle: i64,
    data_ptr: i64,
    data_len: i64,
) -> (i64, i64) {
    validate_buffer!(data_ptr, data_len, err_to_tuple2);

    with_socket_mut!(handle, TcpStream, err_to_tuple2, stream => {
        let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
        match stream.write(data) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Flush a TCP stream's output buffer.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_flush(handle: i64) -> i64 {
    with_socket_mut!(handle, TcpStream, err_to_i64, stream => {
        match stream.flush() {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Shutdown a TCP stream (0=read, 1=write, 2=both).
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_shutdown(handle: i64, how: i64) -> i64 {
    with_socket!(handle, TcpStream, err_to_i64, stream => {
        let shutdown = match how {
            0 => std::net::Shutdown::Read,
            1 => std::net::Shutdown::Write,
            _ => std::net::Shutdown::Both,
        };

        match stream.shutdown(shutdown) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
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
    with_socket!(handle, TcpStream, err_to_i64, stream => {
        match stream.set_nodelay(nodelay != 0) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set keepalive option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_keepalive(handle: i64, keepalive_ns: i64) -> i64 {
    with_socket!(handle, TcpStream, err_to_i64, stream => {
        // Convert to socket2 for keepalive control
        // keepalive_ns > 0 means enable, 0 means disable
        let socket = Socket::from(stream.try_clone().unwrap());
        let enable = keepalive_ns > 0;

        match socket.set_keepalive(enable) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set read timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_read_timeout(handle: i64, timeout_ns: i64) -> i64 {
    with_socket!(handle, TcpStream, err_to_i64, stream => {
        let timeout = if timeout_ns > 0 {
            Some(Duration::from_nanos(timeout_ns as u64))
        } else {
            None
        };

        match stream.set_read_timeout(timeout) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set write timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_tcp_set_write_timeout(handle: i64, timeout_ns: i64) -> i64 {
    with_socket!(handle, TcpStream, err_to_i64, stream => {
        let timeout = if timeout_ns > 0 {
            Some(Duration::from_nanos(timeout_ns as u64))
        } else {
            None
        };

        match stream.set_write_timeout(timeout) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Get TCP_NODELAY option.
/// Returns (nodelay, error_code)
#[no_mangle]
pub extern "C" fn native_tcp_get_nodelay(handle: i64) -> (i64, i64) {
    with_socket!(handle, TcpStream, err_to_tuple2, stream => {
        match stream.nodelay() {
            Ok(nodelay) => (if nodelay { 1 } else { 0 }, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Peek data from a TCP stream without consuming it.
/// Returns (bytes_peeked, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_tcp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple2);

    with_socket!(handle, TcpStream, err_to_tuple2, stream => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match stream.peek(buf) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}
