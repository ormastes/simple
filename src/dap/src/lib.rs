//! Minimal Debug Adapter Protocol (DAP) implementation for Simple language
//!
//! This provides basic debugging functionality:
//! - Breakpoint management
//! - Stack trace inspection
//! - Step through code (step in/over/out)
//! - Variable inspection
//! - Continue/pause execution

pub mod protocol;
pub mod server;
pub mod transport;

pub use server::DapServer;
