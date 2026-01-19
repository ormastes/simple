// Request builder - handles adding response channels to requests

use super::types::{IoRequest, IoResponse, ResponseSender};

/// Adds response channel to a request
pub(crate) fn build_request_with_response(
    request: IoRequest,
    response_tx: ResponseSender,
) -> IoRequest {
    match request {
        IoRequest::TcpListen { addr, .. } => IoRequest::TcpListen { addr, response_tx },
        IoRequest::TcpAccept { listener_id, .. } => IoRequest::TcpAccept {
            listener_id,
            response_tx,
        },
        IoRequest::TcpConnect { addr, .. } => IoRequest::TcpConnect { addr, response_tx },
        IoRequest::TcpRead {
            stream_id, max_len, ..
        } => IoRequest::TcpRead {
            stream_id,
            max_len,
            response_tx,
        },
        IoRequest::TcpWrite {
            stream_id, data, ..
        } => IoRequest::TcpWrite {
            stream_id,
            data,
            response_tx,
        },
        IoRequest::TcpClose { stream_id, .. } => IoRequest::TcpClose {
            stream_id,
            response_tx,
        },
        IoRequest::UdpBind { addr, .. } => IoRequest::UdpBind { addr, response_tx },
        IoRequest::UdpSendTo {
            socket_id, data, addr, ..
        } => IoRequest::UdpSendTo {
            socket_id,
            data,
            addr,
            response_tx,
        },
        IoRequest::UdpRecvFrom {
            socket_id, max_len, ..
        } => IoRequest::UdpRecvFrom {
            socket_id,
            max_len,
            response_tx,
        },
        IoRequest::UdpClose { socket_id, .. } => IoRequest::UdpClose {
            socket_id,
            response_tx,
        },
        IoRequest::TcpSetNodelay {
            stream_id, nodelay, ..
        } => IoRequest::TcpSetNodelay {
            stream_id,
            nodelay,
            response_tx,
        },
        IoRequest::TcpSetKeepalive {
            stream_id, secs, ..
        } => IoRequest::TcpSetKeepalive {
            stream_id,
            secs,
            response_tx,
        },
        IoRequest::TcpShutdown {
            stream_id, how, ..
        } => IoRequest::TcpShutdown {
            stream_id,
            how,
            response_tx,
        },
        IoRequest::TcpListenerClose { listener_id, .. } => IoRequest::TcpListenerClose {
            listener_id,
            response_tx,
        },
        IoRequest::TcpGetLocalAddr { stream_id, .. } => IoRequest::TcpGetLocalAddr {
            stream_id,
            response_tx,
        },
        IoRequest::TcpGetPeerAddr { stream_id, .. } => IoRequest::TcpGetPeerAddr {
            stream_id,
            response_tx,
        },
        IoRequest::UdpSetBroadcast {
            socket_id, broadcast, ..
        } => IoRequest::UdpSetBroadcast {
            socket_id,
            broadcast,
            response_tx,
        },
        IoRequest::UdpSetMulticastTtl { socket_id, ttl, .. } => {
            IoRequest::UdpSetMulticastTtl {
                socket_id,
                ttl,
                response_tx,
            }
        }
        IoRequest::UdpJoinMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            ..
        } => IoRequest::UdpJoinMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            response_tx,
        },
        IoRequest::UdpLeaveMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            ..
        } => IoRequest::UdpLeaveMulticast {
            socket_id,
            multicast_addr,
            interface_addr,
            response_tx,
        },
        IoRequest::UdpGetLocalAddr { socket_id, .. } => IoRequest::UdpGetLocalAddr {
            socket_id,
            response_tx,
        },
        IoRequest::Shutdown => IoRequest::Shutdown,
    }
}
