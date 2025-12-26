//! JSON-RPC transport over stdio
//!
//! Implements the Language Server Protocol / Debug Adapter Protocol message format:
//! Content-Length: <bytes>\r\n
//! \r\n
//! <JSON message>
//!
//! This module is shared between LSP and DAP implementations.

use serde::{Deserialize, Serialize};
use serde_json;
use std::io::{self, BufRead, Write};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TransportError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("Invalid message format: {0}")]
    InvalidFormat(String),
}

/// Read a message from stdin
pub fn read_message<R: BufRead, M: for<'de> Deserialize<'de>>(
    reader: &mut R,
) -> Result<M, TransportError> {
    // Read headers
    let mut content_length: Option<usize> = None;

    loop {
        let mut header = String::new();
        reader.read_line(&mut header)?;

        let header = header.trim();
        if header.is_empty() {
            break;
        }

        if let Some(value) = header.strip_prefix("Content-Length: ") {
            content_length = Some(
                value
                    .parse()
                    .map_err(|_| TransportError::InvalidFormat("Invalid Content-Length".to_string()))?,
            );
        }
    }

    let content_length = content_length
        .ok_or_else(|| TransportError::InvalidFormat("Missing Content-Length header".to_string()))?;

    // Read content
    let mut content = vec![0u8; content_length];
    reader.read_exact(&mut content)?;

    // Parse JSON
    let message: M = serde_json::from_slice(&content)?;
    Ok(message)
}

/// Write a message to stdout
pub fn write_message<W: Write, M: Serialize>(
    writer: &mut W,
    message: &M,
) -> Result<(), TransportError> {
    let content = serde_json::to_string(message)?;
    let content_bytes = content.as_bytes();

    // Write headers
    write!(writer, "Content-Length: {}\r\n\r\n", content_bytes.len())?;

    // Write content
    writer.write_all(content_bytes)?;
    writer.flush()?;

    Ok(())
}
