//! Simple Language Server binary
//!
//! Minimal LSP server for the Simple language providing:
//! - Text document synchronization
//! - Parse error diagnostics

use simple_lsp::LspServer;
use std::process;

fn main() {
    // Initialize tracing (optional)
    tracing_subscriber::fmt()
        .with_writer(std::io::stderr)
        .with_max_level(tracing::Level::INFO)
        .init();

    tracing::info!("Simple LSP server starting");

    let mut server = LspServer::new();

    if let Err(e) = server.run() {
        tracing::error!("LSP server error: {}", e);
        process::exit(1);
    }

    tracing::info!("Simple LSP server exiting");
}
