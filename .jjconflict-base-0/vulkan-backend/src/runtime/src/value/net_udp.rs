// UDP FFI functions for runtime/value/net module

/// Bind a UDP socket to an address.
/// Returns (handle, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64) {
    let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple2);

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
    let addr = parse_addr!(addr_ptr, addr_len, err_to_i64);

    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        match socket.connect(addr) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Receive data from a UDP socket with source address.
/// Returns (bytes_recv, peer_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_recv_from(
    handle: i64,
    buf_ptr: i64,
    buf_len: i64,
) -> (i64, i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple3);

    with_socket!(handle, UdpSocket, err_to_tuple3, socket => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match socket.recv_from(buf) {
            Ok((n, addr)) => {
                let addr_ptr = addr_to_string_ptr(&addr);
                (n as i64, addr_ptr, NetError::Success as i64)
            }
            Err(e) => (0, 0, NetError::from(e) as i64),
        }
    })
}

/// Receive data from a connected UDP socket.
/// Returns (bytes_recv, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_recv(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple2);

    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match socket.recv(buf) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
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
    validate_buffer!(data_ptr, data_len, err_to_tuple2);
    let addr = parse_addr!(addr_ptr, addr_len, err_to_tuple2);

    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
        match socket.send_to(data, addr) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Send data on a connected UDP socket.
/// Returns (bytes_sent, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_send(
    handle: i64,
    data_ptr: i64,
    data_len: i64,
) -> (i64, i64) {
    validate_buffer!(data_ptr, data_len, err_to_tuple2);

    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        let data = std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize);
        match socket.send(data) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Peek data from a UDP socket with source address.
/// Returns (bytes_peeked, peer_addr_ptr, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_peek_from(
    handle: i64,
    buf_ptr: i64,
    buf_len: i64,
) -> (i64, i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple3);

    with_socket!(handle, UdpSocket, err_to_tuple3, socket => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match socket.peek_from(buf) {
            Ok((n, addr)) => {
                let addr_ptr = addr_to_string_ptr(&addr);
                (n as i64, addr_ptr, NetError::Success as i64)
            }
            Err(e) => (0, 0, NetError::from(e) as i64),
        }
    })
}

/// Peek data from a connected UDP socket.
/// Returns (bytes_peeked, error_code)
#[no_mangle]
pub unsafe extern "C" fn native_udp_peek(handle: i64, buf_ptr: i64, buf_len: i64) -> (i64, i64) {
    validate_buffer!(buf_ptr, buf_len, err_to_tuple2);

    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        let buf = std::slice::from_raw_parts_mut(buf_ptr as *mut u8, buf_len as usize);
        match socket.peek(buf) {
            Ok(n) => (n as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Get the connected peer address of a UDP socket.
/// Returns (addr_ptr, error_code)
#[no_mangle]
pub extern "C" fn native_udp_peer_addr(handle: i64) -> (i64, i64) {
    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        match socket.peer_addr() {
            Ok(addr) => {
                let addr_ptr = addr_to_string_ptr(&addr);
                (addr_ptr, NetError::Success as i64)
            }
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Set broadcast option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_broadcast(handle: i64, broadcast: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        match socket.set_broadcast(broadcast != 0) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set multicast loop option.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_multicast_loop(handle: i64, on: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        // Try IPv4 first, then IPv6
        if socket.set_multicast_loop_v4(on != 0).is_ok() {
            return NetError::Success as i64;
        }
        match socket.set_multicast_loop_v6(on != 0) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set multicast TTL.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_multicast_ttl(handle: i64, ttl: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        match socket.set_multicast_ttl_v4(ttl as u32) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set TTL.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_ttl(handle: i64, ttl: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        match socket.set_ttl(ttl as u32) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set read timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_read_timeout(handle: i64, timeout_ns: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        let timeout = if timeout_ns > 0 {
            Some(Duration::from_nanos(timeout_ns as u64))
        } else {
            None
        };

        match socket.set_read_timeout(timeout) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Set write timeout.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_set_write_timeout(handle: i64, timeout_ns: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        let timeout = if timeout_ns > 0 {
            Some(Duration::from_nanos(timeout_ns as u64))
        } else {
            None
        };

        match socket.set_write_timeout(timeout) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Get broadcast option.
/// Returns (broadcast, error_code)
#[no_mangle]
pub extern "C" fn native_udp_get_broadcast(handle: i64) -> (i64, i64) {
    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        match socket.broadcast() {
            Ok(broadcast) => (if broadcast { 1 } else { 0 }, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Get TTL.
/// Returns (ttl, error_code)
#[no_mangle]
pub extern "C" fn native_udp_get_ttl(handle: i64) -> (i64, i64) {
    with_socket!(handle, UdpSocket, err_to_tuple2, socket => {
        match socket.ttl() {
            Ok(ttl) => (ttl as i64, NetError::Success as i64),
            Err(e) => (0, NetError::from(e) as i64),
        }
    })
}

/// Join IPv4 multicast group.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_join_multicast_v4(handle: i64, multiaddr: i64, interface: i64) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        // multiaddr and interface are packed as u32 IPv4 addresses
        let multi = Ipv4Addr::from((multiaddr as u32).to_be_bytes());
        let iface = Ipv4Addr::from((interface as u32).to_be_bytes());

        match socket.join_multicast_v4(&multi, &iface) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Leave IPv4 multicast group.
/// Returns error_code
#[no_mangle]
pub extern "C" fn native_udp_leave_multicast_v4(
    handle: i64,
    multiaddr: i64,
    interface: i64,
) -> i64 {
    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        let multi = Ipv4Addr::from((multiaddr as u32).to_be_bytes());
        let iface = Ipv4Addr::from((interface as u32).to_be_bytes());

        match socket.leave_multicast_v4(&multi, &iface) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Join IPv6 multicast group.
/// Returns error_code
#[no_mangle]
pub unsafe extern "C" fn native_udp_join_multicast_v6(
    handle: i64,
    multiaddr_ptr: i64,
    interface: i64,
) -> i64 {
    if multiaddr_ptr == 0 {
        return NetError::InvalidInput as i64;
    }

    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        // multiaddr_ptr points to 16 bytes of IPv6 address
        let bytes = std::slice::from_raw_parts(multiaddr_ptr as *const u8, 16);
        let mut arr = [0u8; 16];
        arr.copy_from_slice(bytes);
        let multi = Ipv6Addr::from(arr);

        match socket.join_multicast_v6(&multi, interface as u32) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
}

/// Leave IPv6 multicast group.
/// Returns error_code
#[no_mangle]
pub unsafe extern "C" fn native_udp_leave_multicast_v6(
    handle: i64,
    multiaddr_ptr: i64,
    interface: i64,
) -> i64 {
    if multiaddr_ptr == 0 {
        return NetError::InvalidInput as i64;
    }

    with_socket!(handle, UdpSocket, err_to_i64, socket => {
        let bytes = std::slice::from_raw_parts(multiaddr_ptr as *const u8, 16);
        let mut arr = [0u8; 16];
        arr.copy_from_slice(bytes);
        let multi = Ipv6Addr::from(arr);

        match socket.leave_multicast_v6(&multi, interface as u32) {
            Ok(_) => NetError::Success as i64,
            Err(e) => NetError::from(e) as i64,
        }
    })
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
