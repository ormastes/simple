// Request dispatcher - routes requests to appropriate handlers

use super::registry::StreamRegistry;
use super::tcp_handlers::*;
use super::types::IoRequest;
use super::udp_handlers::*;

/// Dispatches a request to the appropriate handler
pub(crate) async fn dispatch_request(request: IoRequest, registry: &mut StreamRegistry) {
    match request {
        IoRequest::TcpListen { addr, response_tx } => {
            handle_tcp_listen(addr, response_tx, registry).await;
        }
        IoRequest::TcpAccept {
            listener_id,
            response_tx,
        } => {
            handle_tcp_accept(listener_id, response_tx, registry).await;
        }
        IoRequest::TcpConnect { addr, response_tx } => {
            handle_tcp_connect(addr, response_tx, registry).await;
        }
        IoRequest::TcpRead {
            stream_id,
            max_len,
            response_tx,
        } => {
            handle_tcp_read(stream_id, max_len, response_tx, registry).await;
        }
        IoRequest::TcpWrite {
            stream_id,
            data,
            response_tx,
        } => {
            handle_tcp_write(stream_id, data, response_tx, registry).await;
        }
        IoRequest::TcpClose { stream_id, response_tx } => {
            handle_tcp_close(stream_id, response_tx, registry);
        }
        IoRequest::UdpBind { addr, response_tx } => {
            handle_udp_bind(addr, response_tx, registry).await;
        }
        IoRequest::UdpSendTo {
            socket_id,
            data,
            addr,
            response_tx,
        } => {
            handle_udp_send_to(socket_id, data, addr, response_tx, registry).await;
        }
        IoRequest::UdpRecvFrom {
            socket_id,
            max_len,
            response_tx,
        } => {
            handle_udp_recv_from(socket_id, max_len, response_tx, registry).await;
        }
        IoRequest::UdpClose { socket_id, response_tx } => {
            handle_udp_close(socket_id, response_tx, registry);
        }
        IoRequest::TcpSetNodelay {
            stream_id,
            nodelay,
            response_tx,
        } => {
            handle_tcp_set_nodelay(stream_id, nodelay, response_tx, registry);
        }
        IoRequest::TcpSetKeepalive {
            stream_id,
            secs,
            response_tx,
        } => {
            handle_tcp_set_keepalive(stream_id, secs, response_tx, registry);
        }
        IoRequest::TcpShutdown {
            stream_id,
            how,
            response_tx,
        } => {
            handle_tcp_shutdown(stream_id, how, response_tx, registry).await;
        }
        IoRequest::TcpListenerClose {
            listener_id,
            response_tx,
        } => {
            handle_tcp_listener_close(listener_id, response_tx, registry);
        }
        IoRequest::TcpGetLocalAddr { stream_id, response_tx } => {
            handle_tcp_get_local_addr(stream_id, response_tx, registry);
        }
        IoRequest::TcpGetPeerAddr { stream_id, response_tx } => {
            handle_tcp_get_peer_addr(stream_id, response_tx, registry);
        }
        IoRequest::UdpSetBroadcast {
            socket_id,
            broadcast,
            response_tx,
        } => {
            handle_udp_set_broadcast(socket_id, broadcast, response_tx, registry);
        }
        IoRequest::UdpSetMulticastTtl {
            socket_id,
            ttl,
            response_tx,
        } => {
            handle_udp_set_multicast_ttl(socket_id, ttl, response_tx, registry);
        }
        IoRequest::UdpJoinMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            response_tx,
        } => {
            handle_udp_join_multicast(socket_id, multicast_addr, interface_addr, response_tx, registry);
        }
        IoRequest::UdpLeaveMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            response_tx,
        } => {
            handle_udp_leave_multicast(socket_id, multicast_addr, interface_addr, response_tx, registry);
        }
        IoRequest::UdpGetLocalAddr { socket_id, response_tx } => {
            handle_udp_get_local_addr(socket_id, response_tx, registry);
        }
        IoRequest::Shutdown => {
            // Handled in main loop
        }
    }
}
