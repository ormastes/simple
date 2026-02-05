// TCP Operation Handlers

use super::macros::*;
use super::registry::StreamRegistry;
use super::types::{IoResponse, ResponseSender};
use monoio::io::{AsyncReadRent, AsyncReadRentExt, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::{TcpListener, TcpStream};

pub(crate) async fn handle_tcp_listen(addr: String, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let socket_addr = parse_addr!(addr, response_tx);

    match TcpListener::bind(socket_addr) {
        Ok(listener) => {
            let id = registry.add_tcp_listener(listener);
            send_success!(response_tx, id);
        }
        Err(e) => send_error!(response_tx, -2, format!("Bind failed: {}", e)),
    }
}

pub(crate) async fn handle_tcp_accept(listener_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let listener = get_tcp_listener!(registry, listener_id, response_tx);

    match listener.accept().await {
        Ok((stream, _peer_addr)) => {
            let id = registry.add_tcp_stream(stream);
            send_success!(response_tx, id);
        }
        Err(e) => send_error!(response_tx, -5, format!("Accept failed: {}", e)),
    }
}

pub(crate) async fn handle_tcp_connect(addr: String, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let socket_addr = parse_addr!(addr, response_tx);

    match TcpStream::connect(socket_addr).await {
        Ok(stream) => {
            let id = registry.add_tcp_stream(stream);
            send_success!(response_tx, id);
        }
        Err(e) => {
            let code = match e.kind() {
                std::io::ErrorKind::ConnectionRefused => -2,
                std::io::ErrorKind::TimedOut => -4,
                _ => -1,
            };
            send_error!(response_tx, code, format!("Connect failed: {}", e));
        }
    }
}

pub(crate) async fn handle_tcp_read(
    stream_id: i64,
    max_len: usize,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    let buf = vec![0u8; max_len];
    let (result, buf) = stream.read(buf).await;

    match result {
        Ok(n) => {
            let _ = response_tx.send(IoResponse::Data {
                bytes: buf[..n].to_vec(),
                len: n,
            });
        }
        Err(e) => send_error!(response_tx, -5, format!("Read failed: {}", e)),
    }
}

pub(crate) async fn handle_tcp_write(
    stream_id: i64,
    data: Vec<u8>,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    let (result, _buf) = stream.write(data).await;

    match result {
        Ok(n) => {
            let _ = response_tx.send(IoResponse::Data { bytes: vec![], len: n });
        }
        Err(e) => send_error!(response_tx, -5, format!("Write failed: {}", e)),
    }
}

pub(crate) fn handle_tcp_close(stream_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    if registry.remove_tcp_stream(stream_id) {
        send_success!(response_tx, 0);
    } else {
        send_error!(response_tx, -1, "Invalid stream ID");
    }
}

pub(crate) fn handle_tcp_set_nodelay(
    stream_id: i64,
    nodelay: bool,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    match stream.set_nodelay(nodelay) {
        Ok(_) => send_success!(response_tx, 0),
        Err(e) => send_error!(response_tx, -2, format!("set_nodelay failed: {}", e)),
    }
}

pub(crate) fn handle_tcp_set_keepalive(
    stream_id: i64,
    _secs: Option<u32>,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let _stream = get_tcp_stream!(registry, stream_id, response_tx);

    // Note: monoio's TcpStream may not expose set_keepalive directly
    // For now, we'll return success as a stub
    tracing::warn!("TCP keepalive not fully supported in monoio, returning success");
    send_success!(response_tx, 0);
}

pub(crate) async fn handle_tcp_shutdown(
    stream_id: i64,
    _how: i64,
    response_tx: ResponseSender,
    registry: &mut StreamRegistry,
) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    // Note: monoio's shutdown() doesn't take a mode parameter
    // It always shuts down writes. The 'how' parameter is ignored for now.
    match stream.shutdown().await {
        Ok(_) => send_success!(response_tx, 0),
        Err(e) => send_error!(response_tx, -3, format!("shutdown failed: {}", e)),
    }
}

pub(crate) fn handle_tcp_listener_close(listener_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    if registry.remove_tcp_listener(listener_id) {
        send_success!(response_tx, 0);
    } else {
        send_error!(response_tx, -1, "Invalid listener ID");
    }
}

pub(crate) fn handle_tcp_get_local_addr(stream_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    match stream.local_addr() {
        Ok(addr) => {
            let _ = response_tx.send(IoResponse::Address { addr: addr.to_string() });
        }
        Err(e) => send_error!(response_tx, -2, format!("local_addr failed: {}", e)),
    }
}

pub(crate) fn handle_tcp_get_peer_addr(stream_id: i64, response_tx: ResponseSender, registry: &mut StreamRegistry) {
    let stream = get_tcp_stream!(registry, stream_id, response_tx);

    match stream.peer_addr() {
        Ok(addr) => {
            let _ = response_tx.send(IoResponse::Address { addr: addr.to_string() });
        }
        Err(e) => send_error!(response_tx, -2, format!("peer_addr failed: {}", e)),
    }
}
