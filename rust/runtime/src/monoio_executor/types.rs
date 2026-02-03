// Operation Types for Monoio Async Executor
// Defines the types for pending I/O operations and their results.

#![cfg(feature = "monoio-direct")]

use std::net::SocketAddr;

/// Type of pending I/O operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpType {
    TcpConnect,
    TcpAccept,
    TcpRead,
    TcpWrite,
    UdpRecvFrom,
    UdpSendTo,
}

/// State of a pending operation
#[derive(Debug)]
pub enum OpState {
    /// Operation not yet started
    NotStarted,
    /// Operation is in progress
    InProgress,
    /// Operation completed successfully
    Completed(OpResult),
    /// Operation failed
    Failed(String),
}

/// Result of a completed operation
#[derive(Debug)]
pub enum OpResult {
    /// Connection handle (for connect/accept)
    Handle(i64),
    /// Bytes transferred (for read/write)
    Bytes(usize),
    /// Data received (for read operations)
    Data(Vec<u8>),
    /// Data with address (for UDP recv_from)
    DataFrom(Vec<u8>, SocketAddr),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_op_type_equality() {
        assert_eq!(OpType::TcpConnect, OpType::TcpConnect);
        assert_ne!(OpType::TcpConnect, OpType::TcpAccept);
    }

    #[test]
    fn test_op_state_match() {
        let state = OpState::NotStarted;
        assert!(matches!(state, OpState::NotStarted));
    }
}
