// Direct I/O FFI functions for monoio
// Feature: monoio-direct
// Provides zero-overhead async I/O by executing on thread-local monoio runtime
//
// This module has been refactored into focused submodules for better maintainability.
// All public FFI functions are re-exported to maintain backward compatibility.

#![cfg(feature = "monoio-direct")]

// Module declarations
mod init;
mod tcp;
mod tcp_options;
mod udp;
mod udp_options;
mod future;
mod stats;

// Re-export all public FFI functions for backward compatibility

// Runtime initialization
pub use init::rt_monoio_init;

// TCP operations
pub use tcp::{
    rt_monoio_tcp_listen,
    rt_monoio_tcp_accept,
    rt_monoio_tcp_connect,
    rt_monoio_tcp_read,
    rt_monoio_tcp_write,
    rt_monoio_tcp_close,
    rt_monoio_tcp_listener_close,
    rt_monoio_tcp_flush,
};

// TCP socket options
pub use tcp_options::{
    rt_monoio_tcp_shutdown,
    rt_monoio_tcp_local_addr,
    rt_monoio_tcp_peer_addr,
    rt_monoio_tcp_set_nodelay,
    rt_monoio_tcp_set_keepalive,
};

// UDP operations
pub use udp::{
    rt_monoio_udp_bind,
    rt_monoio_udp_send_to,
    rt_monoio_udp_recv_from,
    rt_monoio_udp_close,
    rt_monoio_udp_local_addr,
    rt_monoio_udp_connect,
    rt_monoio_udp_send,
    rt_monoio_udp_recv,
};

// UDP socket options
pub use udp_options::{
    rt_monoio_udp_set_broadcast,
    rt_monoio_udp_set_multicast_ttl,
    rt_monoio_udp_join_multicast,
    rt_monoio_udp_leave_multicast,
};

// Async future operations
pub use future::{
    rt_monoio_poll,
    rt_monoio_tcp_read_async,
    rt_monoio_tcp_write_async,
    rt_monoio_tcp_connect_async,
    rt_monoio_tcp_accept_async,
};

// Performance metrics
pub use stats::rt_monoio_direct_stats;

#[cfg(test)]
mod tests {
    // Tests are maintained in individual modules
}
