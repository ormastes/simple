// AsyncExecutor: Core polling and execution logic
// Manages the async runtime and coordinates concurrent operation execution.

#![cfg(feature = "monoio-direct")]

use crate::value::monoio_future::MonoioFuture;
use crate::value::RuntimeValue;
use monoio::net::TcpStream;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::pending_op::PendingOp;
use super::runtime;
use super::tcp_ops::TcpOps;
use super::types::{OpResult, OpState, OpType};
use super::udp_ops::UdpOps;

/// The async executor manages the monoio runtime and pending operations.
///
/// # Architecture
///
/// ```text
/// ┌─────────────────────────────────────────────────────────────┐
/// │ AsyncExecutor (thread-local)                                │
/// │                                                             │
/// │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
/// │  │ TCP Streams │  │ TCP Listen  │  │ UDP Sockets │         │
/// │  │ HandleStore │  │ HandleStore │  │ HandleStore │         │
/// │  └─────────────┘  └─────────────┘  └─────────────┘         │
/// │                                                             │
/// │  ┌─────────────────────────────────────────────────┐       │
/// │  │ Pending Operations (HashMap<u64, PendingOp>)    │       │
/// │  └─────────────────────────────────────────────────┘       │
/// │                                                             │
/// │  ┌─────────────────────────────────────────────────┐       │
/// │  │ Runtime (created on-demand for poll)            │       │
/// │  └─────────────────────────────────────────────────┘       │
/// └─────────────────────────────────────────────────────────────┘
/// ```
pub struct AsyncExecutor {
    /// TCP operations
    tcp_ops: TcpOps,
    /// UDP operations
    udp_ops: UdpOps,
    /// Pending operations
    pending: HashMap<u64, PendingOp>,
    /// Next operation ID
    next_op_id: u64,
    /// io_uring entries configuration
    entries: u32,
    /// Whether executor is initialized
    initialized: bool,
}

impl AsyncExecutor {
    pub fn new() -> Self {
        Self {
            tcp_ops: TcpOps::new(),
            udp_ops: UdpOps::new(),
            pending: HashMap::new(),
            next_op_id: 1,
            entries: 256,
            initialized: false,
        }
    }

    /// Initialize the executor
    pub fn init(&mut self, entries: u32) {
        self.entries = entries;
        self.initialized = true;
    }

    /// Check if initialized
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }

    /// Allocate a new operation ID
    fn alloc_op_id(&mut self) -> u64 {
        let id = self.next_op_id;
        self.next_op_id += 1;
        id
    }

    // ========================================================================
    // TCP Operations
    // ========================================================================

    /// Bind a TCP listener (synchronous, returns immediately)
    pub fn tcp_listen(&mut self, addr: &str) -> Result<i64, String> {
        self.tcp_ops.tcp_listen(addr)
    }

    /// Submit async TCP accept operation
    pub fn tcp_accept_submit(&mut self, listener_id: i64, future_ptr: *mut MonoioFuture) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = self.tcp_ops.tcp_accept_submit(listener_id, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Submit async TCP connect operation
    pub fn tcp_connect_submit(&mut self, addr: &str, future_ptr: *mut MonoioFuture) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = TcpOps::tcp_connect_submit(addr, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Submit async TCP read operation
    pub fn tcp_read_submit(
        &mut self,
        stream_id: i64,
        buffer: RuntimeValue,
        max_len: usize,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = self.tcp_ops.tcp_read_submit(stream_id, buffer, max_len, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Submit async TCP write operation
    pub fn tcp_write_submit(
        &mut self,
        stream_id: i64,
        data: Vec<u8>,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = self.tcp_ops.tcp_write_submit(stream_id, data, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Close a TCP stream
    pub fn tcp_close(&mut self, stream_id: i64) -> bool {
        self.tcp_ops.tcp_close(stream_id)
    }

    /// Close a TCP listener
    pub fn tcp_listener_close(&mut self, listener_id: i64) -> bool {
        self.tcp_ops.tcp_listener_close(listener_id)
    }

    // ========================================================================
    // UDP Operations
    // ========================================================================

    /// Bind a UDP socket (synchronous)
    pub fn udp_bind(&mut self, addr: &str) -> Result<i64, String> {
        self.udp_ops.udp_bind(addr)
    }

    /// Submit async UDP send_to operation
    pub fn udp_send_to_submit(
        &mut self,
        socket_id: i64,
        data: Vec<u8>,
        addr: &str,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = self.udp_ops.udp_send_to_submit(socket_id, data, addr, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Submit async UDP recv_from operation
    pub fn udp_recv_from_submit(
        &mut self,
        socket_id: i64,
        buffer: RuntimeValue,
        max_len: usize,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        let op_id = self.alloc_op_id();
        let op = self.udp_ops.udp_recv_from_submit(socket_id, buffer, max_len, future_ptr, op_id)?;
        self.pending.insert(op_id, op);
        Ok(op_id)
    }

    /// Close a UDP socket
    pub fn udp_close(&mut self, socket_id: i64) -> bool {
        self.udp_ops.udp_close(socket_id)
    }

    // ========================================================================
    // Polling and Execution
    // ========================================================================

    /// Poll all pending operations concurrently.
    ///
    /// This method runs all pending operations in parallel using spawn_local,
    /// providing true non-blocking async behavior. Operations that complete
    /// will have their results stored and state updated.
    ///
    /// Returns the number of operations that completed.
    pub fn poll_all(&mut self) -> usize {
        if self.pending.is_empty() {
            return 0;
        }

        // Collect operations that need execution
        let ops_to_run: Vec<(u64, OpType)> = self
            .pending
            .iter()
            .filter(|(_, op)| matches!(op.state, OpState::NotStarted | OpState::InProgress))
            .map(|(id, op)| (*id, op.op_type))
            .collect();

        if ops_to_run.is_empty() {
            // Remove completed operations
            self.pending
                .retain(|_, op| !matches!(op.state, OpState::Completed(_) | OpState::Failed(_)));
            return 0;
        }

        // Run all operations concurrently
        let completed = self.run_concurrent(ops_to_run);

        // Remove completed operations
        self.pending
            .retain(|_, op| !matches!(op.state, OpState::Completed(_) | OpState::Failed(_)));

        completed
    }

    /// Run multiple operations concurrently using spawn_local.
    fn run_concurrent(&mut self, ops: Vec<(u64, OpType)>) -> usize {
        // Create runtime for concurrent execution
        let mut rt = match monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
            .with_entries(self.entries)
            .build()
        {
            Ok(rt) => rt,
            Err(e) => {
                tracing::error!("Failed to create runtime: {}", e);
                return 0;
            }
        };

        // Prepare results storage
        let results: Rc<RefCell<Vec<(u64, Result<OpResult, String>)>>> = Rc::new(RefCell::new(Vec::new()));

        // Prepare operation data
        let mut op_data: Vec<(
            u64,
            OpType,
            i64,
            Option<String>,
            Option<Vec<u8>>,
            usize,
            Option<RuntimeValue>,
        )> = Vec::new();

        for (op_id, op_type) in &ops {
            if let Some(op) = self.pending.get(op_id) {
                op_data.push((
                    *op_id,
                    *op_type,
                    op.handle_id,
                    op.addr.clone(),
                    op.data.clone(),
                    op.max_len,
                    op.buffer,
                ));
            }
        }

        // Take ownership of handles we need
        let mut taken_listeners = HashMap::new();
        let mut taken_streams = HashMap::new();
        let mut taken_sockets = HashMap::new();

        for (_, op_type, handle_id, _, _, _, _) in &op_data {
            match op_type {
                OpType::TcpAccept => {
                    if let Some(l) = self.tcp_ops.tcp_listeners.take(*handle_id) {
                        taken_listeners.insert(*handle_id, l);
                    }
                }
                OpType::TcpRead | OpType::TcpWrite => {
                    if let Some(s) = self.tcp_ops.tcp_streams.take(*handle_id) {
                        taken_streams.insert(*handle_id, s);
                    }
                }
                OpType::UdpRecvFrom | OpType::UdpSendTo => {
                    if let Some(s) = self.udp_ops.udp_sockets.take(*handle_id) {
                        taken_sockets.insert(*handle_id, s);
                    }
                }
                OpType::TcpConnect => {} // No handle to take
            }
        }

        // Wrap handles in RefCell for sharing
        let listeners = Rc::new(RefCell::new(taken_listeners));
        let streams = Rc::new(RefCell::new(taken_streams));
        let sockets = Rc::new(RefCell::new(taken_sockets));

        // New streams created by accept/connect
        let new_streams: Rc<RefCell<Vec<(u64, TcpStream)>>> = Rc::new(RefCell::new(Vec::new()));

        // Run all operations
        rt.block_on(async {
            let mut handles = Vec::new();

            for (op_id, op_type, handle_id, addr, data, max_len, _buffer) in op_data {
                let results_clone = results.clone();
                let listeners_clone = listeners.clone();
                let streams_clone = streams.clone();
                let sockets_clone = sockets.clone();
                let new_streams_clone = new_streams.clone();

                let handle = monoio::spawn(async move {
                    let result = runtime::execute_operation(
                        op_type,
                        handle_id,
                        addr,
                        data,
                        max_len,
                        &listeners_clone,
                        &streams_clone,
                        &sockets_clone,
                        &new_streams_clone,
                        op_id,
                    )
                    .await;

                    results_clone.borrow_mut().push((op_id, result));
                });

                handles.push(handle);
            }

            // Wait for all operations to complete
            for handle in handles {
                let _ = handle.await;
            }
        });

        // Put handles back
        for (id, listener) in listeners.borrow_mut().drain() {
            self.tcp_ops.tcp_listeners.put_back(id, listener);
        }
        for (id, stream) in streams.borrow_mut().drain() {
            self.tcp_ops.tcp_streams.put_back(id, stream);
        }
        for (id, socket) in sockets.borrow_mut().drain() {
            self.udp_ops.udp_sockets.put_back(id, socket);
        }

        // Process new streams from accept/connect
        let mut stream_ids: HashMap<u64, i64> = HashMap::new();
        for (op_id, stream) in new_streams.borrow_mut().drain(..) {
            let stream_id = self.tcp_ops.tcp_streams.insert(stream);
            stream_ids.insert(op_id, stream_id);
        }

        // Process results
        let mut completed = 0;
        for (op_id, result) in results.borrow_mut().drain(..) {
            if let Some(op) = self.pending.get_mut(&op_id) {
                match result {
                    Ok(mut op_result) => {
                        // Update handle ID for accept/connect results
                        if let OpResult::Handle(_) = &op_result {
                            if let Some(&stream_id) = stream_ids.get(&op_id) {
                                op_result = OpResult::Handle(stream_id);
                            }
                        }
                        op.complete(op_result);
                        completed += 1;
                    }
                    Err(e) => {
                        op.fail(&e);
                        completed += 1;
                    }
                }
            }
        }

        completed
    }

    /// Poll a single operation by ID.
    ///
    /// Returns true if the operation completed (success or failure).
    /// For true async behavior, prefer using poll_all() which runs operations concurrently.
    pub fn poll_one(&mut self, op_id: u64) -> bool {
        let op = match self.pending.get(&op_id) {
            Some(op) => op,
            None => return false,
        };

        // If already completed, nothing to do
        if matches!(op.state, OpState::Completed(_) | OpState::Failed(_)) {
            return true;
        }

        // Run this single operation
        let op_type = op.op_type;
        let completed = self.run_concurrent(vec![(op_id, op_type)]);
        completed > 0
    }

    /// Get the number of pending operations
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Get resource counts
    pub fn resource_counts(&self) -> (usize, usize, usize) {
        (
            self.tcp_ops.stream_count(),
            self.tcp_ops.listener_count(),
            self.udp_ops.socket_count(),
        )
    }
}

impl Default for AsyncExecutor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_executor_init() {
        let mut exec = AsyncExecutor::new();
        exec.init(256);
        assert!(exec.is_initialized());
    }

    #[test]
    fn test_pending_count() {
        let exec = AsyncExecutor::new();
        assert_eq!(exec.pending_count(), 0);
    }
}
