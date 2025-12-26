//! Simple Debug Adapter binary
//!
//! Minimal DAP server for debugging Simple programs providing:
//! - Breakpoint management
//! - Stack trace inspection
//! - Step through code (step in/over/out)
//! - Variable inspection

use simple_dap::DapServer;
use std::process;

fn main() {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_max_level(tracing::Level::INFO)
        .init();

    tracing::info!("Simple DAP server starting");

    let mut server = DapServer::new();

    if let Err(e) = server.run() {
        tracing::error!("DAP server error: {}", e);
        process::exit(1);
    }

    tracing::info!("Simple DAP server exiting");
}
