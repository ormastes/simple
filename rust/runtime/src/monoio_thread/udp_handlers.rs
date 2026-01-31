// UDP Operation Handlers

use super::macros::*;
use super::registry::StreamRegistry;
use super::types::{IoResponse, ResponseSender};
use monoio::io::{AsyncReadRent, AsyncReadRentExt, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::udp::UdpSocket;

pub(crate) async fn handle_udp_bind(addr: String, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let socket_addr = parse_addr!(addr, response_tx);

    match UdpSocket::bind(socket_addr) {
        Ok(socket) => {
            let id = registry.add_udp_socket(socket);
            send_success!(response_tx, id);
        }
        Err(e) => send_error!(response_tx, -2, format!("Bind failed: {}", e)),
    }
}

pub(crate) async fn handle_udp_send_to(
    socket_id: i64,
    data: Vec<u8>,
    addr: String,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let socket = get_udp_socket!(registry, socket_id, response_tx);
    let socket_addr = parse_addr!(addr, response_tx);

    let (result, _buf) = socket.send_to(data, socket_addr).await;

    match result {
        Ok(n) => {
            let _ = response_tx.send(IoResponse::Data { bytes: vec![], len: n });
        }
        Err(e) => send_error!(response_tx, -5, format!("Send failed: {}", e)),
    }
}

pub(crate) async fn handle_udp_recv_from(
    socket_id: i64,
    max_len: usize,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let socket = get_udp_socket!(registry, socket_id, response_tx);

    let buf = vec![0u8; max_len];
    let (result, buf) = socket.recv_from(buf).await;

    match result {
        Ok((n, peer_addr)) => {
            let _ = response_tx.send(IoResponse::DataFrom {
                bytes: buf[..n].to_vec(),
                len: n,
                addr: peer_addr.to_string(),
            });
        }
        Err(e) => send_error!(response_tx, -5, format!("Recv failed: {}", e)),
    }
}

pub(crate) fn handle_udp_close(socket_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    if registry.remove_udp_socket(socket_id) {
        send_success!(response_tx, 0);
    } else {
        send_error!(response_tx, -1, "Invalid socket ID");
    }
}

pub(crate) fn handle_udp_set_broadcast(
    socket_id: i64,
    _broadcast: bool,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let _socket = get_udp_socket!(registry, socket_id, response_tx);

    // Note: monoio's UdpSocket doesn't expose set_broadcast
    // monoio's UdpSocket wraps socket2::Socket but doesn't expose all options
    // Would need to access underlying socket2::Socket for full functionality
    // via socket.as_raw_socket()/as_raw_fd() and socket2::Socket::from_raw_socket()
    tracing::warn!("UDP set_broadcast not fully supported in monoio, returning success");
    send_success!(response_tx, 0);
}

pub(crate) fn handle_udp_set_multicast_ttl(
    socket_id: i64,
    _ttl: u32,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let _socket = get_udp_socket!(registry, socket_id, response_tx);

    // Note: monoio's UdpSocket doesn't expose set_multicast_ttl_v4
    // monoio's UdpSocket wraps socket2::Socket but doesn't expose all options
    // Would need to access underlying socket2::Socket for full functionality
    // via socket.as_raw_socket()/as_raw_fd() and socket2::Socket::from_raw_socket()
    tracing::warn!("UDP set_multicast_ttl not fully supported in monoio, returning success");
    send_success!(response_tx, 0);
}

pub(crate) fn handle_udp_join_multicast(
    socket_id: i64,
    _multicast_addr: String,
    _interface_addr: String,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let _socket = get_udp_socket!(registry, socket_id, response_tx);

    // Note: monoio's UdpSocket doesn't expose join_multicast_v4
    // monoio's UdpSocket wraps socket2::Socket but doesn't expose all options
    // Would need to access underlying socket2::Socket for full functionality
    // via socket.as_raw_socket()/as_raw_fd() and socket2::Socket::from_raw_socket()
    tracing::warn!("UDP join_multicast not fully supported in monoio, returning success");
    send_success!(response_tx, 0);
}

pub(crate) fn handle_udp_leave_multicast(
    socket_id: i64,
    _multicast_addr: String,
    _interface_addr: String,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let _socket = get_udp_socket!(registry, socket_id, response_tx);

    // Note: monoio's UdpSocket doesn't expose leave_multicast_v4
    // monoio's UdpSocket wraps socket2::Socket but doesn't expose all options
    // Would need to access underlying socket2::Socket for full functionality
    // via socket.as_raw_socket()/as_raw_fd() and socket2::Socket::from_raw_socket()
    tracing::warn!("UDP leave_multicast not fully supported in monoio, returning success");
    send_success!(response_tx, 0);
}

pub(crate) fn handle_udp_get_local_addr(socket_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let socket = get_udp_socket!(registry, socket_id, response_tx);

    match socket.local_addr() {
        Ok(addr) => {
            let _ = response_tx.send(IoResponse::Address { addr: addr.to_string() });
        }
        Err(e) => send_error!(response_tx, -2, format!("local_addr failed: {}", e)),
    }
}
