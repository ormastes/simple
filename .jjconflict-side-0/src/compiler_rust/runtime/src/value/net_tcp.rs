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
    close_socket(handle)
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

// Use macro to generate timeout setters
impl_timeout_setter!(native_tcp_set_read_timeout, TcpStream, set_read_timeout);
impl_timeout_setter!(native_tcp_set_write_timeout, TcpStream, set_write_timeout);

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

fn runtime_text_ptr_len(text: crate::value::RuntimeValue) -> Option<(i64, i64)> {
    let ptr = crate::value::collections::rt_string_data(text);
    if ptr.is_null() {
        return None;
    }
    let len = crate::value::collections::rt_string_len(text);
    if len < 0 {
        return None;
    }
    Some((ptr as i64, len))
}

fn runtime_byte_array_to_vec(data: crate::value::RuntimeValue) -> Option<Vec<u8>> {
    let len = crate::value::collections::rt_array_len(data);
    if len < 0 {
        return None;
    }
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = crate::value::collections::rt_array_get(data, i);
        if !value.is_int() {
            return None;
        }
        let byte = value.as_int();
        if !(0..=255).contains(&byte) {
            return None;
        }
        out.push(byte as u8);
    }
    Some(out)
}

fn timeout_from_optional_ms(ms: crate::value::RuntimeValue) -> Option<Duration> {
    if ms.is_nil() {
        return None;
    }
    if !ms.is_int() {
        return None;
    }
    let millis = ms.as_int();
    if millis < 0 {
        None
    } else {
        Some(Duration::from_millis(millis as u64))
    }
}

/// Simple-facing TCP bind wrapper.
#[no_mangle]
pub extern "C" fn rt_io_tcp_bind(addr: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(addr) else {
        return -(NetError::InvalidAddress as i64);
    };
    let (handle, err) = unsafe { native_tcp_bind(ptr, len) };
    if err == NetError::Success as i64 { handle } else { -err }
}

/// Simple-facing TCP accept wrapper.
#[no_mangle]
pub extern "C" fn rt_io_tcp_accept(handle: i64) -> i64 {
    let (stream_handle, _peer_addr, err) = native_tcp_accept(handle);
    if err == NetError::Success as i64 {
        stream_handle
    } else {
        -err
    }
}

/// Simple-facing TCP accept with timeout wrapper.
#[no_mangle]
pub extern "C" fn rt_io_tcp_accept_timeout(handle: i64, ms: i64) -> i64 {
    let deadline = if ms <= 0 {
        None
    } else {
        Some(std::time::Instant::now() + Duration::from_millis(ms as u64))
    };

    loop {
        let accept_result = {
            let registry = SOCKET_REGISTRY.lock().unwrap();
            let entry = match registry.get(&handle) {
                Some(e) => e,
                None => return -(NetError::InvalidHandle as i64),
            };
            let listener = match entry {
                SocketEntry::TcpListener(l) => l,
                _ => return -(NetError::InvalidHandle as i64),
            };
            let _ = listener.set_nonblocking(true);
            let result = listener.accept();
            let _ = listener.set_nonblocking(false);
            result
        };

        match accept_result {
            Ok((stream, _peer)) => return register_tcp_stream(stream),
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                if let Some(limit) = deadline {
                    if std::time::Instant::now() >= limit {
                        return -(NetError::TimedOut as i64);
                    }
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            Err(e) => return -(NetError::from(e) as i64),
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_connect(addr: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(addr) else {
        return -(NetError::InvalidAddress as i64);
    };
    let (handle, _local_addr, err) = unsafe { native_tcp_connect(ptr, len) };
    if err == NetError::Success as i64 { handle } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_connect_timeout(addr: crate::value::RuntimeValue, ms: i64) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(addr) else {
        return -(NetError::InvalidAddress as i64);
    };
    let timeout_ns = if ms <= 0 { 0 } else { ms.saturating_mul(1_000_000) };
    let (handle, _local_addr, err) = unsafe { native_tcp_connect_timeout(ptr, len, timeout_ns) };
    if err == NetError::Success as i64 { handle } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_read(handle: i64, size: i64) -> crate::value::RuntimeValue {
    if size <= 0 {
        return crate::value::collections::rt_array_new(0);
    }
    let mut buffer = vec![0u8; size as usize];
    let (read, err) = unsafe { native_tcp_read(handle, buffer.as_mut_ptr() as i64, size) };
    if err != NetError::Success as i64 || read <= 0 {
        return crate::value::collections::rt_array_new(0);
    }
    unsafe { crate::value::ffi::file_io::rt_bytes_from_raw(buffer.as_ptr() as i64, read) }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_read_line(handle: i64) -> crate::value::RuntimeValue {
    let mut bytes = Vec::new();
    with_socket_mut!(handle, TcpStream, |_| crate::value::RuntimeValue::NIL, stream => {
        let mut one = [0u8; 1];
        loop {
            match stream.read(&mut one) {
                Ok(0) => break,
                Ok(_) => {
                    bytes.push(one[0]);
                    if one[0] == b'\n' {
                        break;
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                Err(_) => return crate::value::RuntimeValue::NIL,
            }
        }
        if bytes.is_empty() {
            crate::value::RuntimeValue::NIL
        } else {
            unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_write(handle: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some(bytes) = runtime_byte_array_to_vec(data) else {
        return -1;
    };
    let (written, err) = unsafe { native_tcp_write(handle, bytes.as_ptr() as i64, bytes.len() as i64) };
    if err == NetError::Success as i64 { written } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_write_text(handle: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(data) else {
        return -1;
    };
    let (written, err) = unsafe { native_tcp_write(handle, ptr, len) };
    if err == NetError::Success as i64 { written } else { -err }
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_flush(handle: i64) -> bool {
    native_tcp_flush(handle) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_close(handle: i64) -> bool {
    native_tcp_close(handle) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_local_addr(handle: i64) -> crate::value::RuntimeValue {
    with_socket!(handle, TcpListener, |_| {
        with_socket!(handle, TcpStream, |_| crate::value::RuntimeValue::NIL, stream => match stream.local_addr() {
            Ok(addr) => {
                let text = addr.to_string();
                unsafe { crate::value::collections::rt_string_new(text.as_ptr(), text.len() as u64) }
            }
            Err(_) => crate::value::RuntimeValue::NIL,
        })
    }, listener => match listener.local_addr() {
        Ok(addr) => {
            let text = addr.to_string();
            unsafe { crate::value::collections::rt_string_new(text.as_ptr(), text.len() as u64) }
        }
        Err(_) => crate::value::RuntimeValue::NIL,
    })
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_peer_addr(handle: i64) -> crate::value::RuntimeValue {
    with_socket!(handle, TcpStream, |_| crate::value::RuntimeValue::NIL, stream => match stream.peer_addr() {
        Ok(addr) => {
            let text = addr.to_string();
            unsafe { crate::value::collections::rt_string_new(text.as_ptr(), text.len() as u64) }
        }
        Err(_) => crate::value::RuntimeValue::NIL,
    })
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_set_nodelay(handle: i64, enabled: bool) -> bool {
    native_tcp_set_nodelay(handle, if enabled { 1 } else { 0 }) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_set_read_timeout(handle: i64, ms: crate::value::RuntimeValue) -> bool {
    let timeout = timeout_from_optional_ms(ms);
    let nanos = timeout.map(|d| d.as_nanos() as i64).unwrap_or(-1);
    native_tcp_set_read_timeout(handle, nanos) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_set_write_timeout(handle: i64, ms: crate::value::RuntimeValue) -> bool {
    let timeout = timeout_from_optional_ms(ms);
    let nanos = timeout.map(|d| d.as_nanos() as i64).unwrap_or(-1);
    native_tcp_set_write_timeout(handle, nanos) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_tcp_shutdown(handle: i64, how: i64) -> bool {
    native_tcp_shutdown(handle, how) == NetError::Success as i64
}
