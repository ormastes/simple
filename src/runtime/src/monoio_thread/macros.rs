// Helper Macros for Reducing Duplication

use super::types::{IoResponse, ResponseSender};

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
    ($tx:expr, $id:expr) => {{
        let _ = $tx.send(IoResponse::Success { id: $id });
    }};
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
        match $addr.parse::<std::net::SocketAddr>() {
            Ok(a) => a,
            Err(e) => send_error!($tx, -1, format!("Invalid address: {}", e)),
        }
    };
}

pub(crate) use {
    get_tcp_listener, get_tcp_stream, get_udp_socket, parse_addr, send_error, send_success,
};
