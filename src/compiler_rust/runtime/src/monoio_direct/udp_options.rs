// UDP socket options for direct monoio I/O
// Feature: monoio-direct

use crate::monoio_runtime::direct::with_registry;
use crate::value::RuntimeValue;

// ============================================================================
// UDP Socket Options
// ============================================================================

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
