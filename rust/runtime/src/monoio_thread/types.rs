// Request/Response Types

/// Requests sent from FFI to runtime thread
#[derive(Debug)]
pub enum IoRequest {
    // TCP operations
    TcpListen {
        addr: String,
        response_tx: ResponseSender,
    },
    TcpAccept {
        listener_id: i64,
        response_tx: ResponseSender,
    },
    TcpConnect {
        addr: String,
        response_tx: ResponseSender,
    },
    TcpRead {
        stream_id: i64,
        max_len: usize,
        response_tx: ResponseSender,
    },
    TcpWrite {
        stream_id: i64,
        data: Vec<u8>,
        response_tx: ResponseSender,
    },
    TcpClose {
        stream_id: i64,
        response_tx: ResponseSender,
    },

    // UDP operations
    UdpBind {
        addr: String,
        response_tx: ResponseSender,
    },
    UdpSendTo {
        socket_id: i64,
        data: Vec<u8>,
        addr: String,
        response_tx: ResponseSender,
    },
    UdpRecvFrom {
        socket_id: i64,
        max_len: usize,
        response_tx: ResponseSender,
    },
    UdpClose {
        socket_id: i64,
        response_tx: ResponseSender,
    },

    // TCP socket options
    TcpSetNodelay {
        stream_id: i64,
        nodelay: bool,
        response_tx: ResponseSender,
    },
    TcpSetKeepalive {
        stream_id: i64,
        secs: Option<u32>,
        response_tx: ResponseSender,
    },
    TcpShutdown {
        stream_id: i64,
        how: i64,
        response_tx: ResponseSender,
    },
    TcpListenerClose {
        listener_id: i64,
        response_tx: ResponseSender,
    },
    TcpGetLocalAddr {
        stream_id: i64,
        response_tx: ResponseSender,
    },
    TcpGetPeerAddr {
        stream_id: i64,
        response_tx: ResponseSender,
    },

    // UDP socket options
    UdpSetBroadcast {
        socket_id: i64,
        broadcast: bool,
        response_tx: ResponseSender,
    },
    UdpSetMulticastTtl {
        socket_id: i64,
        ttl: u32,
        response_tx: ResponseSender,
    },
    UdpJoinMulticast {
        socket_id: i64,
        multicast_addr: String,
        interface_addr: String,
        response_tx: ResponseSender,
    },
    UdpLeaveMulticast {
        socket_id: i64,
        multicast_addr: String,
        interface_addr: String,
        response_tx: ResponseSender,
    },
    UdpGetLocalAddr {
        socket_id: i64,
        response_tx: ResponseSender,
    },

    // Shutdown
    Shutdown,
}

/// Responses sent from runtime thread back to FFI
#[derive(Debug, Clone)]
pub enum IoResponse {
    Success { id: i64 },
    Error { code: i64, message: String },
    Data { bytes: Vec<u8>, len: usize },
    DataFrom { bytes: Vec<u8>, len: usize, addr: String },
    Address { addr: String },
}

pub type ResponseSender = std::sync::mpsc::Sender<IoResponse>;
