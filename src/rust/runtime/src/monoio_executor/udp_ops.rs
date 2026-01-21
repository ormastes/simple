// UDP Operations for AsyncExecutor
// Handles UDP socket binding, sending, and receiving.

#![cfg(feature = "monoio-direct")]

use crate::value::monoio_future::MonoioFuture;
use crate::value::RuntimeValue;
use monoio::net::udp::UdpSocket;
use std::net::SocketAddr;

use super::handle_store::HandleStore;
use super::pending_op::PendingOp;
use super::types::OpType;

/// UDP-specific operations for AsyncExecutor
pub struct UdpOps {
    /// UDP sockets
    pub(super) udp_sockets: HandleStore<UdpSocket>,
}

impl UdpOps {
    pub fn new() -> Self {
        Self {
            udp_sockets: HandleStore::new(),
        }
    }

    /// Bind a UDP socket (synchronous)
    pub fn udp_bind(&mut self, addr: &str) -> Result<i64, String> {
        let socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let socket = UdpSocket::bind(socket_addr).map_err(|e| format!("Bind failed: {}", e))?;

        Ok(self.udp_sockets.insert(socket))
    }

    /// Submit async UDP send_to operation
    pub fn udp_send_to_submit(
        &mut self,
        socket_id: i64,
        data: Vec<u8>,
        addr: &str,
        future_ptr: *mut MonoioFuture,
        op_id: u64,
    ) -> Result<PendingOp, String> {
        if !self.udp_sockets.is_available(socket_id) {
            return Err("Invalid socket ID".to_string());
        }

        let mut op = PendingOp::with_handle(op_id, OpType::UdpSendTo, future_ptr, socket_id);
        op.data = Some(data);
        op.addr = Some(addr.to_string());

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = socket_id;
            }
        }

        Ok(op)
    }

    /// Submit async UDP recv_from operation
    pub fn udp_recv_from_submit(
        &mut self,
        socket_id: i64,
        buffer: RuntimeValue,
        max_len: usize,
        future_ptr: *mut MonoioFuture,
        op_id: u64,
    ) -> Result<PendingOp, String> {
        if !self.udp_sockets.is_available(socket_id) {
            return Err("Invalid socket ID".to_string());
        }

        let mut op = PendingOp::with_handle(op_id, OpType::UdpRecvFrom, future_ptr, socket_id);
        op.buffer = Some(buffer);
        op.max_len = max_len;

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = socket_id;
            }
        }

        Ok(op)
    }

    /// Close a UDP socket
    pub fn udp_close(&mut self, socket_id: i64) -> bool {
        self.udp_sockets.remove(socket_id).is_some()
    }

    /// Get socket count
    pub fn socket_count(&self) -> usize {
        self.udp_sockets.len()
    }
}

impl Default for UdpOps {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_udp_ops_new() {
        let ops = UdpOps::new();
        assert_eq!(ops.socket_count(), 0);
    }
}
