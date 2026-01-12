// Monoio runtime thread with message passing
// Solves the !Send/!Sync problem by running monoio on a dedicated thread
// FFI calls send messages to this thread via channels

#![cfg(feature = "monoio-net")]

use crate::value::RuntimeValue;
use monoio::io::{AsyncReadRent, AsyncReadRentExt, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::udp::UdpSocket;
use monoio::net::{TcpListener, TcpStream};
use parking_lot::RwLock;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::{Arc, Mutex, Once};
use std::thread;

// ============================================================================
// Helper Macros for Reducing Duplication
// ============================================================================

/// Send error response and return early
macro_rules! send_error {
    ($tx:expr, $code:expr, $msg:expr) => {{
        let _ = $tx.send(IoResponse::Error {
            code: $code,
            message: $msg.to_string(),
        });
        return;
    }};
}

/// Send success response
macro_rules! send_success {
    ($tx:expr, $id:expr) => {
        let _ = $tx.send(IoResponse::Success { id: $id });
    };
}

/// Get TCP stream from registry or send error and return
macro_rules! get_tcp_stream {
    ($registry:expr, $id:expr, $tx:expr) => {
        match $registry.get_tcp_stream($id) {
            Some(s) => s,
            None => send_error!($tx, -1, "Invalid stream ID"),
        }
    };
}

/// Get TCP listener from registry or send error and return
macro_rules! get_tcp_listener {
    ($registry:expr, $id:expr, $tx:expr) => {
        match $registry.get_tcp_listener($id) {
            Some(l) => l,
            None => send_error!($tx, -1, "Invalid listener ID"),
        }
    };
}

/// Get UDP socket from registry or send error and return
macro_rules! get_udp_socket {
    ($registry:expr, $id:expr, $tx:expr) => {
        match $registry.get_udp_socket($id) {
            Some(s) => s,
            None => send_error!($tx, -1, "Invalid socket ID"),
        }
    };
}

/// Parse socket address or send error and return
macro_rules! parse_addr {
    ($addr:expr, $tx:expr) => {
        match $addr.parse::<SocketAddr>() {
            Ok(a) => a,
            Err(e) => send_error!($tx, -1, format!("Invalid address: {}", e)),
        }
    };
}

// ============================================================================
// Request/Response Types
// ============================================================================

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
    Success {
        id: i64,
    },
    Error {
        code: i64,
        message: String,
    },
    Data {
        bytes: Vec<u8>,
        len: usize,
    },
    DataFrom {
        bytes: Vec<u8>,
        len: usize,
        addr: String,
    },
    Address {
        addr: String,
    },
}

type ResponseSender = std::sync::mpsc::Sender<IoResponse>;

// ============================================================================
// Stream Registry
// ============================================================================

/// Stores active TCP/UDP connections
struct StreamRegistry {
    next_id: i64,
    tcp_listeners: HashMap<i64, TcpListener>,
    tcp_streams: HashMap<i64, TcpStream>,
    udp_sockets: HashMap<i64, UdpSocket>,
}

impl StreamRegistry {
    fn new() -> Self {
        Self {
            next_id: 1,
            tcp_listeners: HashMap::new(),
            tcp_streams: HashMap::new(),
            udp_sockets: HashMap::new(),
        }
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn add_tcp_listener(&mut self, listener: TcpListener) -> i64 {
        let id = self.alloc_id();
        self.tcp_listeners.insert(id, listener);
        id
    }

    fn add_tcp_stream(&mut self, stream: TcpStream) -> i64 {
        let id = self.alloc_id();
        self.tcp_streams.insert(id, stream);
        id
    }

    fn add_udp_socket(&mut self, socket: UdpSocket) -> i64 {
        let id = self.alloc_id();
        self.udp_sockets.insert(id, socket);
        id
    }

    fn get_tcp_listener(&mut self, id: i64) -> Option<&mut TcpListener> {
        self.tcp_listeners.get_mut(&id)
    }

    fn get_tcp_stream(&mut self, id: i64) -> Option<&mut TcpStream> {
        self.tcp_streams.get_mut(&id)
    }

    fn get_udp_socket(&mut self, id: i64) -> Option<&mut UdpSocket> {
        self.udp_sockets.get_mut(&id)
    }

    fn remove_tcp_listener(&mut self, id: i64) -> bool {
        self.tcp_listeners.remove(&id).is_some()
    }

    fn remove_tcp_stream(&mut self, id: i64) -> bool {
        self.tcp_streams.remove(&id).is_some()
    }

    fn remove_udp_socket(&mut self, id: i64) -> bool {
        self.udp_sockets.remove(&id).is_some()
    }
}

// ============================================================================
// Global Runtime Thread
// ============================================================================

lazy_static::lazy_static! {
    static ref RUNTIME_THREAD: RuntimeThread = RuntimeThread::new();
}

struct RuntimeThread {
    request_tx: std::sync::mpsc::Sender<IoRequest>,
}

impl RuntimeThread {
    fn new() -> Self {
        let (request_tx, request_rx) = std::sync::mpsc::channel::<IoRequest>();

        // Spawn the runtime thread
        thread::Builder::new()
            .name("monoio-runtime".to_string())
            .spawn(move || {
                Self::runtime_thread_main(request_rx);
            })
            .expect("Failed to spawn monoio runtime thread");

        tracing::info!("Monoio runtime thread started");

        Self { request_tx }
    }

    fn runtime_thread_main(request_rx: std::sync::mpsc::Receiver<IoRequest>) {
        // Create monoio runtime
        let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
            .with_entries(256)
            .build()
            .expect("Failed to create monoio runtime");

        // Run the event loop
        rt.block_on(async move {
            let mut registry = StreamRegistry::new();

            loop {
                // Receive request from FFI
                let request = match request_rx.recv() {
                    Ok(req) => req,
                    Err(_) => {
                        tracing::info!("Request channel closed, shutting down runtime");
                        break;
                    }
                };

                match request {
                    IoRequest::Shutdown => {
                        tracing::info!("Shutdown requested");
                        break;
                    }
                    _ => {
                        Self::handle_request(request, &mut registry).await;
                    }
                }
            }

            tracing::info!("Monoio runtime thread exiting");
        });
    }

    async fn handle_request(request: IoRequest, registry: &mut StreamRegistry) {
        match request {
            IoRequest::TcpListen { addr, response_tx } => {
                Self::handle_tcp_listen(addr, response_tx, registry).await;
            }
            IoRequest::TcpAccept {
                listener_id,
                response_tx,
            } => {
                Self::handle_tcp_accept(listener_id, response_tx, registry).await;
            }
            IoRequest::TcpConnect { addr, response_tx } => {
                Self::handle_tcp_connect(addr, response_tx, registry).await;
            }
            IoRequest::TcpRead {
                stream_id,
                max_len,
                response_tx,
            } => {
                Self::handle_tcp_read(stream_id, max_len, response_tx, registry).await;
            }
            IoRequest::TcpWrite {
                stream_id,
                data,
                response_tx,
            } => {
                Self::handle_tcp_write(stream_id, data, response_tx, registry).await;
            }
            IoRequest::TcpClose {
                stream_id,
                response_tx,
            } => {
                Self::handle_tcp_close(stream_id, response_tx, registry);
            }
            IoRequest::UdpBind { addr, response_tx } => {
                Self::handle_udp_bind(addr, response_tx, registry).await;
            }
            IoRequest::UdpSendTo {
                socket_id,
                data,
                addr,
                response_tx,
            } => {
                Self::handle_udp_send_to(socket_id, data, addr, response_tx, registry).await;
            }
            IoRequest::UdpRecvFrom {
                socket_id,
                max_len,
                response_tx,
            } => {
                Self::handle_udp_recv_from(socket_id, max_len, response_tx, registry).await;
            }
            IoRequest::UdpClose {
                socket_id,
                response_tx,
            } => {
                Self::handle_udp_close(socket_id, response_tx, registry);
            }
            IoRequest::TcpSetNodelay {
                stream_id,
                nodelay,
                response_tx,
            } => {
                Self::handle_tcp_set_nodelay(stream_id, nodelay, response_tx, registry);
            }
            IoRequest::TcpSetKeepalive {
                stream_id,
                secs,
                response_tx,
            } => {
                Self::handle_tcp_set_keepalive(stream_id, secs, response_tx, registry);
            }
            IoRequest::TcpShutdown {
                stream_id,
                how,
                response_tx,
            } => {
                Self::handle_tcp_shutdown(stream_id, how, response_tx, registry).await;
            }
            IoRequest::TcpListenerClose {
                listener_id,
                response_tx,
            } => {
                Self::handle_tcp_listener_close(listener_id, response_tx, registry);
            }
            IoRequest::TcpGetLocalAddr {
                stream_id,
                response_tx,
            } => {
                Self::handle_tcp_get_local_addr(stream_id, response_tx, registry);
            }
            IoRequest::TcpGetPeerAddr {
                stream_id,
                response_tx,
            } => {
                Self::handle_tcp_get_peer_addr(stream_id, response_tx, registry);
            }
            IoRequest::UdpSetBroadcast {
                socket_id,
                broadcast,
                response_tx,
            } => {
                Self::handle_udp_set_broadcast(socket_id, broadcast, response_tx, registry);
            }
            IoRequest::UdpSetMulticastTtl {
                socket_id,
                ttl,
                response_tx,
            } => {
                Self::handle_udp_set_multicast_ttl(socket_id, ttl, response_tx, registry);
            }
            IoRequest::UdpJoinMulticast {
                socket_id,
                multicast_addr,
                interface_addr,
                response_tx,
            } => {
                Self::handle_udp_join_multicast(
                    socket_id,
                    multicast_addr,
                    interface_addr,
                    response_tx,
                    registry,
                );
            }
            IoRequest::UdpLeaveMulticast {
                socket_id,
                multicast_addr,
                interface_addr,
                response_tx,
            } => {
                Self::handle_udp_leave_multicast(
                    socket_id,
                    multicast_addr,
                    interface_addr,
                    response_tx,
                    registry,
                );
            }
            IoRequest::UdpGetLocalAddr {
                socket_id,
                response_tx,
            } => {
                Self::handle_udp_get_local_addr(socket_id, response_tx, registry);
            }
            IoRequest::Shutdown => {
                // Handled in main loop
            }
        }
    }

    // TCP Handlers
    async fn handle_tcp_listen(
        addr: String,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let socket_addr = parse_addr!(addr, response_tx);

        match TcpListener::bind(socket_addr) {
            Ok(listener) => {
                let id = registry.add_tcp_listener(listener);
                send_success!(response_tx, id);
            }
            Err(e) => send_error!(response_tx, -2, format!("Bind failed: {}", e)),
        }
    }

    async fn handle_tcp_accept(
        listener_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let listener = get_tcp_listener!(registry, listener_id, response_tx);

        match listener.accept().await {
            Ok((stream, _peer_addr)) => {
                let id = registry.add_tcp_stream(stream);
                send_success!(response_tx, id);
            }
            Err(e) => send_error!(response_tx, -5, format!("Accept failed: {}", e)),
        }
    }

    async fn handle_tcp_connect(
        addr: String,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
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

    async fn handle_tcp_read(
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

    async fn handle_tcp_write(
        stream_id: i64,
        data: Vec<u8>,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let stream = get_tcp_stream!(registry, stream_id, response_tx);

        let (result, _buf) = stream.write(data).await;

        match result {
            Ok(n) => {
                let _ = response_tx.send(IoResponse::Data {
                    bytes: vec![],
                    len: n,
                });
            }
            Err(e) => send_error!(response_tx, -5, format!("Write failed: {}", e)),
        }
    }

    fn handle_tcp_close(
        stream_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        if registry.remove_tcp_stream(stream_id) {
            send_success!(response_tx, 0);
        } else {
            send_error!(response_tx, -1, "Invalid stream ID");
        }
    }

    // UDP Handlers
    async fn handle_udp_bind(
        addr: String,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let socket_addr = parse_addr!(addr, response_tx);

        match UdpSocket::bind(socket_addr) {
            Ok(socket) => {
                let id = registry.add_udp_socket(socket);
                send_success!(response_tx, id);
            }
            Err(e) => send_error!(response_tx, -2, format!("Bind failed: {}", e)),
        }
    }

    async fn handle_udp_send_to(
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
                let _ = response_tx.send(IoResponse::Data {
                    bytes: vec![],
                    len: n,
                });
            }
            Err(e) => send_error!(response_tx, -5, format!("Send failed: {}", e)),
        }
    }

    async fn handle_udp_recv_from(
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

    fn handle_udp_close(
        socket_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        if registry.remove_udp_socket(socket_id) {
            send_success!(response_tx, 0);
        } else {
            send_error!(response_tx, -1, "Invalid socket ID");
        }
    }

    // TCP Socket Option Handlers

    fn handle_tcp_set_nodelay(
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

    fn handle_tcp_set_keepalive(
        stream_id: i64,
        secs: Option<u32>,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let _stream = get_tcp_stream!(registry, stream_id, response_tx);

        // Note: monoio's TcpStream may not expose set_keepalive directly
        // For now, we'll return success as a stub
        tracing::warn!("TCP keepalive not fully supported in monoio, returning success");
        send_success!(response_tx, 0);
    }

    async fn handle_tcp_shutdown(
        stream_id: i64,
        how: i64,
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

    fn handle_tcp_listener_close(
        listener_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        if registry.remove_tcp_listener(listener_id) {
            send_success!(response_tx, 0);
        } else {
            send_error!(response_tx, -1, "Invalid listener ID");
        }
    }

    fn handle_tcp_get_local_addr(
        stream_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let stream = get_tcp_stream!(registry, stream_id, response_tx);

        match stream.local_addr() {
            Ok(addr) => {
                let _ = response_tx.send(IoResponse::Address {
                    addr: addr.to_string(),
                });
            }
            Err(e) => send_error!(response_tx, -2, format!("local_addr failed: {}", e)),
        }
    }

    fn handle_tcp_get_peer_addr(
        stream_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let stream = get_tcp_stream!(registry, stream_id, response_tx);

        match stream.peer_addr() {
            Ok(addr) => {
                let _ = response_tx.send(IoResponse::Address {
                    addr: addr.to_string(),
                });
            }
            Err(e) => send_error!(response_tx, -2, format!("peer_addr failed: {}", e)),
        }
    }

    // UDP Socket Option Handlers

    fn handle_udp_set_broadcast(
        socket_id: i64,
        broadcast: bool,
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

    fn handle_udp_set_multicast_ttl(
        socket_id: i64,
        ttl: u32,
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

    fn handle_udp_join_multicast(
        socket_id: i64,
        multicast_addr: String,
        interface_addr: String,
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

    fn handle_udp_leave_multicast(
        socket_id: i64,
        multicast_addr: String,
        interface_addr: String,
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

    fn handle_udp_get_local_addr(
        socket_id: i64,
        response_tx: ResponseSender,
        registry: &mut StreamRegistry,
    ) {
        let socket = get_udp_socket!(registry, socket_id, response_tx);

        match socket.local_addr() {
            Ok(addr) => {
                let _ = response_tx.send(IoResponse::Address {
                    addr: addr.to_string(),
                });
            }
            Err(e) => send_error!(response_tx, -2, format!("local_addr failed: {}", e)),
        }
    }

    /// Send a request and wait for response
    pub fn send_request(&self, request: IoRequest) -> IoResponse {
        let (response_tx, response_rx) = std::sync::mpsc::channel();

        // Add response channel to request
        let request_with_tx = match request {
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
                socket_id,
                data,
                addr,
                ..
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
            IoRequest::TcpShutdown { stream_id, how, .. } => IoRequest::TcpShutdown {
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
                socket_id,
                broadcast,
                ..
            } => IoRequest::UdpSetBroadcast {
                socket_id,
                broadcast,
                response_tx,
            },
            IoRequest::UdpSetMulticastTtl { socket_id, ttl, .. } => IoRequest::UdpSetMulticastTtl {
                socket_id,
                ttl,
                response_tx,
            },
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
        };

        // Send request to runtime thread
        if let Err(e) = self.request_tx.send(request_with_tx) {
            return IoResponse::Error {
                code: -1,
                message: format!("Failed to send request: {}", e),
            };
        }

        // Wait for response
        match response_rx.recv() {
            Ok(response) => response,
            Err(e) => IoResponse::Error {
                code: -1,
                message: format!("Failed to receive response: {}", e),
            },
        }
    }
}

// ============================================================================
// Public API for FFI
// ============================================================================

/// Initialize the runtime thread (called once)
pub fn init_runtime_thread() {
    // Access the lazy_static to ensure thread is started
    let _ = &*RUNTIME_THREAD;
}

/// Send a request to the runtime thread and wait for response
pub fn send_request(request: IoRequest) -> IoResponse {
    RUNTIME_THREAD.send_request(request)
}
