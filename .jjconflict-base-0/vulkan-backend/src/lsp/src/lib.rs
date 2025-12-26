//! Minimal Language Server Protocol implementation for Simple language
//!
//! This provides basic LSP functionality:
//! - Text document synchronization
//! - Parse error diagnostics
//! - Server lifecycle management

pub mod protocol;
pub mod server;
pub mod transport;

pub use server::LspServer;
