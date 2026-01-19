// TCP Operations for AsyncExecutor
// Handles TCP listening, accepting, connecting, reading, and writing.

#![cfg(feature = "monoio-direct")]

use crate::value::monoio_future::MonoioFuture;
use crate::value::RuntimeValue;
use monoio::net::{TcpListener, TcpStream};
use std::net::SocketAddr;

use super::handle_store::HandleStore;
use super::pending_op::PendingOp;
use super::types::OpType;

/// TCP-specific operations for AsyncExecutor
pub struct TcpOps {
    /// TCP streams
    pub(super) tcp_streams: HandleStore<TcpStream>,
    /// TCP listeners
    pub(super) tcp_listeners: HandleStore<TcpListener>,
}

impl TcpOps {
    pub fn new() -> Self {
        Self {
            tcp_streams: HandleStore::new(),
            tcp_listeners: HandleStore::new(),
        }
    }

    /// Bind a TCP listener (synchronous, returns immediately)
    pub fn tcp_listen(&mut self, addr: &str) -> Result<i64, String> {
        let socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let listener = TcpListener::bind(socket_addr).map_err(|e| format!("Bind failed: {}", e))?;

        Ok(self.tcp_listeners.insert(listener))
    }

    /// Submit async TCP accept operation
    pub fn tcp_accept_submit(&mut self, listener_id: i64, future_ptr: *mut MonoioFuture, op_id: u64) -> Result<PendingOp, String> {
        if !self.tcp_listeners.is_available(listener_id) {
            return Err("Invalid listener ID".to_string());
        }

        let mut op = PendingOp::with_handle(op_id, OpType::TcpAccept, future_ptr, listener_id);
        op.max_len = listener_id as usize; // Keep for backwards compatibility
        Ok(op)
    }

    /// Submit async TCP connect operation
    pub fn tcp_connect_submit(addr: &str, future_ptr: *mut MonoioFuture, op_id: u64) -> Result<PendingOp, String> {
        let _socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let mut op = PendingOp::new(op_id, OpType::TcpConnect, future_ptr);
        op.addr = Some(addr.to_string());
        Ok(op)
    }

    /// Submit async TCP read operation
    pub fn tcp_read_submit(
        &mut self,
        stream_id: i64,
        buffer: RuntimeValue,
        max_len: usize,
        future_ptr: *mut MonoioFuture,
        op_id: u64,
    ) -> Result<PendingOp, String> {
        if !self.tcp_streams.is_available(stream_id) {
            return Err("Invalid stream ID".to_string());
        }

        let mut op = PendingOp::with_handle(op_id, OpType::TcpRead, future_ptr, stream_id);
        op.buffer = Some(buffer);
        op.max_len = max_len;

        // Store stream_id for execution
        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = stream_id;
            }
        }

        Ok(op)
    }

    /// Submit async TCP write operation
    pub fn tcp_write_submit(
        &mut self,
        stream_id: i64,
        data: Vec<u8>,
        future_ptr: *mut MonoioFuture,
        op_id: u64,
    ) -> Result<PendingOp, String> {
        if !self.tcp_streams.is_available(stream_id) {
            return Err("Invalid stream ID".to_string());
        }

        let mut op = PendingOp::with_handle(op_id, OpType::TcpWrite, future_ptr, stream_id);
        op.data = Some(data);

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = stream_id;
            }
        }

        Ok(op)
    }

    /// Close a TCP stream
    pub fn tcp_close(&mut self, stream_id: i64) -> bool {
        self.tcp_streams.remove(stream_id).is_some()
    }

    /// Close a TCP listener
    pub fn tcp_listener_close(&mut self, listener_id: i64) -> bool {
        self.tcp_listeners.remove(listener_id).is_some()
    }

    /// Get stream count
    pub fn stream_count(&self) -> usize {
        self.tcp_streams.len()
    }

    /// Get listener count
    pub fn listener_count(&self) -> usize {
        self.tcp_listeners.len()
    }
}

impl Default for TcpOps {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tcp_ops_new() {
        let ops = TcpOps::new();
        assert_eq!(ops.stream_count(), 0);
        assert_eq!(ops.listener_count(), 0);
    }

    #[test]
    fn test_tcp_connect_submit() {
        let result = TcpOps::tcp_connect_submit("127.0.0.1:8080", std::ptr::null_mut(), 1);
        assert!(result.is_ok());
        let op = result.unwrap();
        assert_eq!(op.id, 1);
        assert_eq!(op.op_type, OpType::TcpConnect);
    }
}
