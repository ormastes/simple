//! JSON-RPC transport over stdio for LSP
//!
//! Re-exports the shared transport utilities from simple-common.

use crate::protocol::Message;
pub use simple_common::protocol::{
    read_message as read_generic, write_message as write_generic, TransportError,
};
use std::io::{BufRead, Write};

/// Read an LSP message from stdin
pub fn read_message<R: BufRead>(reader: &mut R) -> Result<Message, TransportError> {
    read_generic(reader)
}

/// Write an LSP message to stdout
pub fn write_message<W: Write>(writer: &mut W, message: &Message) -> Result<(), TransportError> {
    write_generic(writer, message)
}
