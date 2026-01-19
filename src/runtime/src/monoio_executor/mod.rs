// Monoio Async Executor Module
// Provides a persistent runtime with non-blocking async I/O operations.
//
// # True Async Architecture
//
// Operations are submitted and return immediately. The executor stores operation
// state and can be polled to advance all pending operations concurrently.
//
// ```text
// 1. Submit Operation  ->  PendingOp created (NotStarted)
// 2. poll_all()        ->  All pending ops run concurrently via spawn_local
// 3. Check completion  ->  Operations move to Completed/Failed state
// ```

#![cfg(feature = "monoio-direct")]

// Module declarations
mod executor;
mod ffi;
mod handle_store;
mod pending_op;
mod runtime;
mod tcp_ops;
mod types;
mod udp_ops;

// Re-export public types for backward compatibility
pub use executor::AsyncExecutor;
pub use ffi::with_executor;
pub use handle_store::HandleStore;
pub use pending_op::PendingOp;
pub use types::{OpResult, OpState, OpType};

// Re-export FFI functions
pub use ffi::{
    rt_monoio_async_init, rt_monoio_async_pending_count, rt_monoio_async_poll_all,
    rt_monoio_async_poll_one, rt_monoio_async_tcp_accept, rt_monoio_async_tcp_close,
    rt_monoio_async_tcp_connect, rt_monoio_async_tcp_listen, rt_monoio_async_tcp_listener_close,
    rt_monoio_async_tcp_read, rt_monoio_async_tcp_write, rt_monoio_async_udp_bind,
    rt_monoio_async_udp_close,
};
