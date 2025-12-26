//! Shared protocol utilities for LSP and DAP

pub mod transport;

pub use transport::{read_message, write_message, TransportError};
