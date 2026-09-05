// UDP SFFI functions for runtime/value/net module

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

// Use macro to generate timeout setters
impl_timeout_setter!(native_udp_set_read_timeout, UdpSocket, set_read_timeout);
impl_timeout_setter!(native_udp_set_write_timeout, UdpSocket, set_write_timeout);

#[no_mangle]
pub extern "C" fn rt_io_udp_set_read_timeout(handle: i64, ms: i64) -> bool {
    native_udp_set_read_timeout(handle, timeout_nanos_from_ms(ms)) == NetError::Success as i64
}

#[no_mangle]
pub extern "C" fn rt_io_udp_set_nonblocking(handle: i64, enabled: bool) -> bool {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
        return false;
    };
    socket.set_nonblocking(enabled).is_ok()
}

#[no_mangle]
pub extern "C" fn rt_io_udp_set_multicast_loop(handle: i64, enabled: bool) -> bool {
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
        return false;
    };
    match socket.local_addr().map(|address| address.ip()) {
        Ok(std::net::IpAddr::V4(_)) => socket.set_multicast_loop_v4(enabled).is_ok(),
        Ok(std::net::IpAddr::V6(_)) => socket.set_multicast_loop_v6(enabled).is_ok(),
        Err(_) => false,
    }
}

fn runtime_multicast_addr(value: crate::value::RuntimeValue) -> Option<std::net::IpAddr> {
    let (ptr, len) = runtime_text_ptr_len(value)?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    std::str::from_utf8(bytes).ok()?.parse().ok()
}

fn rt_io_udp_multicast_membership(
    handle: i64,
    multicast_addr: crate::value::RuntimeValue,
    join: bool,
) -> bool {
    let Some(multicast_addr) = runtime_multicast_addr(multicast_addr) else {
        return false;
    };
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
        return false;
    };
    match multicast_addr {
        std::net::IpAddr::V4(address) => {
            if join {
                socket.join_multicast_v4(&address, &std::net::Ipv4Addr::UNSPECIFIED).is_ok()
            } else {
                socket.leave_multicast_v4(&address, &std::net::Ipv4Addr::UNSPECIFIED).is_ok()
            }
        }
        std::net::IpAddr::V6(address) => {
            if join {
                socket.join_multicast_v6(&address, 0).is_ok()
            } else {
                socket.leave_multicast_v6(&address, 0).is_ok()
            }
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_io_udp_join_multicast(
    handle: i64,
    multicast_addr: crate::value::RuntimeValue,
) -> bool {
    rt_io_udp_multicast_membership(handle, multicast_addr, true)
}

#[no_mangle]
pub extern "C" fn rt_io_udp_leave_multicast(
    handle: i64,
    multicast_addr: crate::value::RuntimeValue,
) -> bool {
    rt_io_udp_multicast_membership(handle, multicast_addr, false)
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
    close_socket(handle)
}

#[no_mangle]
pub extern "C" fn rt_io_udp_set_broadcast(handle: i64, enabled: bool) -> bool {
    native_udp_set_broadcast(handle, if enabled { 1 } else { 0 }) == NetError::Success as i64
}

/// Simple-facing UDP connect contract. Address validation and socket lookup
/// happen once; the hot path adds no allocation or secondary dispatch.
#[no_mangle]
pub extern "C" fn rt_io_udp_connect(handle: i64, addr: crate::value::RuntimeValue) -> bool {
    let Some((ptr, len)) = runtime_text_ptr_len(addr) else {
        return false;
    };
    unsafe { native_udp_connect(handle, ptr, len) == NetError::Success as i64 }
}

const UDP_MAX_PAYLOAD: i64 = 65_535;

fn runtime_packed_bytes(value: crate::value::RuntimeValue) -> Option<(*mut u8, usize)> {
    if value.heap_type() != Some(crate::value::HeapObjectType::Array) {
        return None;
    }
    let array = value.as_heap_ptr() as *mut crate::value::RuntimeArray;
    unsafe {
        if !(*array).is_byte_packed() || (*array).len > (*array).capacity {
            return None;
        }
        if (*array).len > 0 && (*array).data.is_null() {
            return None;
        }
        Some(((*array).data as *mut u8, (*array).len as usize))
    }
}

fn udp_receive_buffer(size: i64) -> Option<(crate::value::RuntimeValue, *mut u8)> {
    if !(0..=UDP_MAX_PAYLOAD).contains(&size) {
        return None;
    }
    let array = crate::value::collections::rt_byte_array_new(size as u64);
    let Some((data, _)) = runtime_packed_bytes(array) else {
        if !array.is_nil() {
            crate::value::collections::rt_array_free(array);
        }
        return None;
    };
    Some((array, data))
}

struct SocketAddrText {
    bytes: [u8; 64],
    len: usize,
    overflowed: bool,
}

impl std::fmt::Write for SocketAddrText {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        let end = self.len.saturating_add(text.len());
        if end > self.bytes.len() {
            self.overflowed = true;
            return Err(std::fmt::Error);
        }
        self.bytes[self.len..end].copy_from_slice(text.as_bytes());
        self.len = end;
        Ok(())
    }
}

fn runtime_socket_addr_text(addr: &SocketAddr) -> crate::value::RuntimeValue {
    let mut text = SocketAddrText {
        bytes: [0; 64],
        len: 0,
        overflowed: false,
    };
    if std::fmt::write(&mut text, format_args!("{addr}")).is_err() || text.overflowed {
        return crate::value::RuntimeValue::NIL;
    }
    crate::value::collections::rt_string_new(text.bytes.as_ptr(), text.len as u64)
}

#[no_mangle]
pub extern "C" fn rt_io_udp_recv(handle: i64, size: i64) -> crate::value::RuntimeValue {
    let Some((array, data)) = udp_receive_buffer(size) else {
        return crate::value::RuntimeValue::NIL;
    };
    let result = {
        let registry = SOCKET_REGISTRY.lock().unwrap();
        let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
            crate::value::collections::rt_array_free(array);
            return crate::value::RuntimeValue::NIL;
        };
        let buffer = unsafe { std::slice::from_raw_parts_mut(data, size as usize) };
        socket.recv(buffer)
    };
    let Ok(received) = result else {
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    };
    let header = crate::value::collections::rt_array_header_ptr(array);
    if !crate::value::collections::rt_array_set_len_known(header, received as i64) {
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    }
    array
}

#[no_mangle]
pub extern "C" fn rt_io_udp_recv_from(handle: i64, size: i64) -> crate::value::RuntimeValue {
    let Some((array, data)) = udp_receive_buffer(size) else {
        return crate::value::RuntimeValue::NIL;
    };
    let result = {
        let registry = SOCKET_REGISTRY.lock().unwrap();
        let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
            crate::value::collections::rt_array_free(array);
            return crate::value::RuntimeValue::NIL;
        };
        let buffer = unsafe { std::slice::from_raw_parts_mut(data, size as usize) };
        socket.recv_from(buffer)
    };
    let Ok((received, peer)) = result else {
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    };
    let header = crate::value::collections::rt_array_header_ptr(array);
    if !crate::value::collections::rt_array_set_len_known(header, received as i64) {
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    }
    let address = runtime_socket_addr_text(&peer);
    if address.is_nil() {
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    }
    let tuple = crate::value::collections::rt_tuple_new(2);
    if tuple.is_nil() {
        crate::value::collections::rt_string_free(address);
        crate::value::collections::rt_array_free(array);
        return crate::value::RuntimeValue::NIL;
    }
    crate::value::collections::rt_tuple_set(tuple, 0, array);
    crate::value::collections::rt_tuple_set(tuple, 1, address);
    tuple
}

#[no_mangle]
pub extern "C" fn rt_io_udp_send(handle: i64, data: crate::value::RuntimeValue) -> i64 {
    let Some((data, len)) = runtime_packed_bytes(data) else {
        return -(NetError::InvalidInput as i64);
    };
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
        return -(NetError::InvalidHandle as i64);
    };
    let bytes = unsafe { std::slice::from_raw_parts(data, len) };
    socket.send(bytes).map(|sent| sent as i64).unwrap_or_else(|error| -(NetError::from(error) as i64))
}

#[no_mangle]
pub extern "C" fn rt_io_udp_send_to(
    handle: i64,
    data: crate::value::RuntimeValue,
    addr: crate::value::RuntimeValue,
) -> i64 {
    let Some((data, len)) = runtime_packed_bytes(data) else {
        return -(NetError::InvalidInput as i64);
    };
    let Some((addr_ptr, addr_len)) = runtime_text_ptr_len(addr) else {
        return -(NetError::InvalidAddress as i64);
    };
    let address = unsafe {
        match parse_socket_addr(addr_ptr, addr_len) {
            Ok(address) => address,
            Err(error) => return -(error as i64),
        }
    };
    let registry = SOCKET_REGISTRY.lock().unwrap();
    let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
        return -(NetError::InvalidHandle as i64);
    };
    let bytes = unsafe { std::slice::from_raw_parts(data, len) };
    socket
        .send_to(bytes, address)
        .map(|sent| sent as i64)
        .unwrap_or_else(|error| -(NetError::from(error) as i64))
}

#[no_mangle]
pub extern "C" fn rt_io_udp_local_addr(handle: i64) -> crate::value::RuntimeValue {
    let result = {
        let registry = SOCKET_REGISTRY.lock().unwrap();
        let Some(SocketEntry::UdpSocket(socket)) = registry.get(&handle) else {
            return crate::value::RuntimeValue::NIL;
        };
        socket.local_addr()
    };
    result
        .map(|address| runtime_socket_addr_text(&address))
        .unwrap_or(crate::value::RuntimeValue::NIL)
}

/// Simple-facing UDP bind contract: a negative value means bind failed.
#[no_mangle]
pub extern "C" fn rt_io_udp_bind(addr: crate::value::RuntimeValue) -> i64 {
    let Some((ptr, len)) = runtime_text_ptr_len(addr) else {
        return -(NetError::InvalidAddress as i64);
    };
    let (handle, err) = unsafe { native_udp_bind(ptr, len) };
    if err == NetError::Success as i64 { handle } else { -err }
}

/// Simple-facing close contract: false means the handle was not live.
#[no_mangle]
pub extern "C" fn rt_io_udp_close(handle: i64) -> bool {
    native_udp_close(handle) == NetError::Success as i64
}

#[cfg(test)]
mod udp_contract_tests {
    use super::*;

    fn runtime_text(text: &str) -> crate::value::RuntimeValue {
        crate::value::collections::rt_string_new(text.as_ptr(), text.len() as u64)
    }

    #[test]
    fn invalid_udp_close_is_false() {
        assert!(!rt_io_udp_close(-1));
    }

    #[test]
    fn invalid_udp_bind_is_negative() {
        assert!(rt_io_udp_bind(crate::value::RuntimeValue::NIL) < 0);
    }

    #[test]
    fn invalid_udp_option_inputs_fail_closed() {
        assert!(!rt_io_udp_connect(-1, crate::value::RuntimeValue::NIL));
        assert!(!rt_io_udp_set_broadcast(-1, true));
        assert!(!rt_io_udp_set_read_timeout(-1, 1));
        assert!(!rt_io_udp_set_nonblocking(-1, true));
    }

    #[test]
    fn invalid_udp_data_inputs_do_not_fabricate_empty_success() {
        assert!(rt_io_udp_recv(-1, 1).is_nil());
        assert!(rt_io_udp_recv_from(-1, 1).is_nil());
        assert!(rt_io_udp_recv(-1, -1).is_nil());
        assert!(rt_io_udp_recv_from(-1, 65_536).is_nil());
        assert!(rt_io_udp_send(-1, crate::value::RuntimeValue::NIL) < 0);
        assert!(rt_io_udp_send_to(
            -1,
            crate::value::RuntimeValue::NIL,
            crate::value::RuntimeValue::NIL,
        ) < 0);
        assert!(rt_io_udp_local_addr(-1).is_nil());
    }

    #[test]
    fn zero_length_datagram_is_some_empty_with_peer_address() {
        let receiver_bind = runtime_text("127.0.0.1:0");
        let sender_bind = runtime_text("127.0.0.1:0");
        let receiver = rt_io_udp_bind(receiver_bind);
        let sender = rt_io_udp_bind(sender_bind);
        assert!(receiver > 0 && sender > 0);

        let receiver_addr = rt_io_udp_local_addr(receiver);
        assert!(!receiver_addr.is_nil());
        let empty = crate::value::collections::rt_byte_array_new(0);
        assert_eq!(rt_io_udp_send_to(sender, empty, receiver_addr), 0);

        let datagram = rt_io_udp_recv_from(receiver, 1);
        assert!(!datagram.is_nil());
        let payload = crate::value::collections::rt_tuple_get(datagram, 0);
        let peer = crate::value::collections::rt_tuple_get(datagram, 1);
        assert_eq!(crate::value::collections::rt_array_len(payload), 0);
        assert!(crate::value::collections::rt_string_len(peer) > 0);

        assert!(rt_io_udp_close(receiver));
        assert!(rt_io_udp_close(sender));
        crate::value::collections::rt_array_free(empty);
        crate::value::collections::rt_array_free(payload);
        crate::value::collections::rt_string_free(peer);
        crate::value::collections::rt_tuple_free(datagram);
        crate::value::collections::rt_string_free(receiver_addr);
        crate::value::collections::rt_string_free(receiver_bind);
        crate::value::collections::rt_string_free(sender_bind);
    }
}
