// Monoio runtime thread with message passing
// Solves the !Send/!Sync problem by running monoio on a dedicated thread
// FFI calls send messages to this thread via channels

#![cfg(feature = "monoio-net")]

// Module declarations
mod dispatcher;
mod macros;
mod registry;
mod request_builder;
mod runtime;
mod tcp_handlers;
mod types;
mod udp_handlers;

// Public re-exports for backward compatibility
pub use runtime::{init_runtime_thread, send_request};
pub use types::{IoRequest, IoResponse};
