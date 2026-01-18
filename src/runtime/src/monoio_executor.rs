// Monoio Async Executor: True non-blocking async I/O
// Feature: monoio-direct
//
// Provides a persistent runtime with non-blocking operations that return
// immediately and can be polled for completion.
//
// # True Async Architecture
//
// Operations are submitted and return immediately. The executor stores operation
// state and can be polled to advance all pending operations concurrently.
//
// ```text
// 1. Submit Operation  ->  PendingOp created (NotStarted)
// 2. poll_all()        ->  All pending ops run concurrently via spawn_local
// 3. Check completion  ->  Operations move to Completed/Failed state
// ```

#![cfg(feature = "monoio-direct")]

use crate::monoio_buffer::OwnedBuf;
use crate::value::monoio_future::{MonoioFuture, FUTURE_STATE_ERROR, FUTURE_STATE_PENDING, FUTURE_STATE_READY};
use crate::value::{HeapHeader, HeapObjectType, RuntimeValue};
use monoio::io::{AsyncReadRent, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::{TcpListener, TcpStream};
use monoio::net::udp::UdpSocket;
use std::cell::RefCell;
use std::collections::HashMap;
use std::future::Future;
use std::net::SocketAddr;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Waker};

// ============================================================================
// Operation Types
// ============================================================================

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

// ============================================================================
// Pending Operation
// ============================================================================

/// Tracks a pending async I/O operation
pub struct PendingOp {
    /// Unique operation ID
    pub id: u64,
    /// Type of operation
    pub op_type: OpType,
    /// Current state
    pub state: OpState,
    /// Associated MonoioFuture (for updating when complete)
    pub future_ptr: *mut MonoioFuture,
    /// Buffer for read operations
    pub buffer: Option<RuntimeValue>,
    /// Max length for read operations
    pub max_len: usize,
    /// Handle ID for the I/O resource (stream, listener, socket)
    pub handle_id: i64,
    /// Address string for connect operations
    pub addr: Option<String>,
    /// Data for write operations
    pub data: Option<Vec<u8>>,
    /// Completion flag (shared with spawned task)
    pub completed: Option<Arc<AtomicBool>>,
    /// Result shared cell (for spawned tasks to store results)
    pub shared_result: Option<Rc<RefCell<Option<Result<OpResult, String>>>>>,
}

impl PendingOp {
    pub fn new(id: u64, op_type: OpType, future_ptr: *mut MonoioFuture) -> Self {
        Self {
            id,
            op_type,
            state: OpState::NotStarted,
            future_ptr,
            buffer: None,
            max_len: 0,
            handle_id: -1,
            addr: None,
            data: None,
            completed: None,
            shared_result: None,
        }
    }

    /// Create a new operation with handle ID
    pub fn with_handle(id: u64, op_type: OpType, future_ptr: *mut MonoioFuture, handle_id: i64) -> Self {
        let mut op = Self::new(id, op_type, future_ptr);
        op.handle_id = handle_id;
        op
    }

    /// Prepare for async execution by setting up shared state
    pub fn prepare_async(&mut self) {
        self.completed = Some(Arc::new(AtomicBool::new(false)));
        self.shared_result = Some(Rc::new(RefCell::new(None)));
        self.state = OpState::InProgress;
    }

    /// Check if the async operation has completed
    pub fn is_async_complete(&self) -> bool {
        self.completed
            .as_ref()
            .map(|c| c.load(Ordering::SeqCst))
            .unwrap_or(false)
    }

    /// Take the async result if available
    pub fn take_async_result(&mut self) -> Option<Result<OpResult, String>> {
        self.shared_result.as_ref().and_then(|r| r.borrow_mut().take())
    }

    /// Mark operation as completed and update the MonoioFuture
    pub fn complete(&mut self, result: OpResult) {
        unsafe {
            if !self.future_ptr.is_null() {
                let future = &mut *self.future_ptr;

                // Convert OpResult to RuntimeValue
                let value = match &result {
                    OpResult::Handle(h) => RuntimeValue::from_int(*h),
                    OpResult::Bytes(n) => RuntimeValue::from_int(*n as i64),
                    OpResult::Data(data) => {
                        // Copy data to buffer if provided
                        if let Some(buf) = self.buffer {
                            let copied = crate::monoio_runtime::copy_to_buffer(buf, data);
                            RuntimeValue::from_int(copied)
                        } else {
                            RuntimeValue::from_int(data.len() as i64)
                        }
                    }
                    OpResult::DataFrom(data, _addr) => {
                        if let Some(buf) = self.buffer {
                            let copied = crate::monoio_runtime::copy_to_buffer(buf, data);
                            RuntimeValue::from_int(copied)
                        } else {
                            RuntimeValue::from_int(data.len() as i64)
                        }
                    }
                };

                future.result = value;
                future.state = FUTURE_STATE_READY;
            }
        }
        self.state = OpState::Completed(result);
    }

    /// Mark operation as failed
    pub fn fail(&mut self, error: &str) {
        self.state = OpState::Failed(error.to_string());

        unsafe {
            if !self.future_ptr.is_null() {
                let future = &mut *self.future_ptr;
                future.result = RuntimeValue::from_int(-1);
                future.state = FUTURE_STATE_ERROR;
            }
        }
    }
}

// ============================================================================
// I/O Handle Storage (with stable IDs)
// ============================================================================

/// Stores I/O handles with stable IDs that don't change
pub struct HandleStore<T> {
    next_id: i64,
    handles: HashMap<i64, Option<T>>,
}

impl<T> HandleStore<T> {
    pub fn new() -> Self {
        Self {
            next_id: 1,
            handles: HashMap::new(),
        }
    }

    /// Insert a handle and return its stable ID
    pub fn insert(&mut self, handle: T) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        self.handles.insert(id, Some(handle));
        id
    }

    /// Get a reference to a handle
    pub fn get(&self, id: i64) -> Option<&T> {
        self.handles.get(&id).and_then(|h| h.as_ref())
    }

    /// Get a mutable reference to a handle
    pub fn get_mut(&mut self, id: i64) -> Option<&mut T> {
        self.handles.get_mut(&id).and_then(|h| h.as_mut())
    }

    /// Take a handle temporarily (for async operations)
    pub fn take(&mut self, id: i64) -> Option<T> {
        self.handles.get_mut(&id).and_then(|h| h.take())
    }

    /// Return a handle after async operation
    pub fn put_back(&mut self, id: i64, handle: T) {
        if let Some(slot) = self.handles.get_mut(&id) {
            *slot = Some(handle);
        }
    }

    /// Remove a handle permanently
    pub fn remove(&mut self, id: i64) -> Option<T> {
        self.handles.remove(&id).flatten()
    }

    /// Check if a handle exists and is available
    pub fn is_available(&self, id: i64) -> bool {
        self.handles.get(&id).map(|h| h.is_some()).unwrap_or(false)
    }

    /// Count of active handles
    pub fn len(&self) -> usize {
        self.handles.values().filter(|h| h.is_some()).count()
    }
}

impl<T> Default for HandleStore<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Async Executor
// ============================================================================

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
    /// TCP streams
    tcp_streams: HandleStore<TcpStream>,
    /// TCP listeners
    tcp_listeners: HandleStore<TcpListener>,
    /// UDP sockets
    udp_sockets: HandleStore<UdpSocket>,
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
            tcp_streams: HandleStore::new(),
            tcp_listeners: HandleStore::new(),
            udp_sockets: HandleStore::new(),
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

    /// Execute an async operation with a new runtime
    fn execute_async<F, R>(&self, future: F) -> Result<R, std::io::Error>
    where
        F: std::future::Future<Output = std::io::Result<R>>,
    {
        let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
            .with_entries(self.entries)
            .build()
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("Failed to create runtime: {}", e)))?;
        rt.block_on(future)
    }

    // ========================================================================
    // TCP Operations
    // ========================================================================

    /// Bind a TCP listener (synchronous, returns immediately)
    pub fn tcp_listen(&mut self, addr: &str) -> Result<i64, String> {
        let socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let listener = TcpListener::bind(socket_addr).map_err(|e| format!("Bind failed: {}", e))?;

        Ok(self.tcp_listeners.insert(listener))
    }

    /// Submit async TCP accept operation
    pub fn tcp_accept_submit(&mut self, listener_id: i64, future_ptr: *mut MonoioFuture) -> Result<u64, String> {
        if !self.tcp_listeners.is_available(listener_id) {
            return Err("Invalid listener ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::with_handle(op_id, OpType::TcpAccept, future_ptr, listener_id);
        op.max_len = listener_id as usize; // Keep for backwards compatibility
        self.pending.insert(op_id, op);

        Ok(op_id)
    }

    /// Submit async TCP connect operation
    pub fn tcp_connect_submit(&mut self, addr: &str, future_ptr: *mut MonoioFuture) -> Result<u64, String> {
        let _socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::new(op_id, OpType::TcpConnect, future_ptr);
        op.addr = Some(addr.to_string());
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
        if !self.tcp_streams.is_available(stream_id) {
            return Err("Invalid stream ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::with_handle(op_id, OpType::TcpRead, future_ptr, stream_id);
        op.buffer = Some(buffer);
        op.max_len = max_len;
        self.pending.insert(op_id, op);

        // Store stream_id for execution
        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = stream_id;
            }
        }

        Ok(op_id)
    }

    /// Submit async TCP write operation
    pub fn tcp_write_submit(
        &mut self,
        stream_id: i64,
        data: Vec<u8>,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        if !self.tcp_streams.is_available(stream_id) {
            return Err("Invalid stream ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::with_handle(op_id, OpType::TcpWrite, future_ptr, stream_id);
        op.data = Some(data);
        self.pending.insert(op_id, op);

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = stream_id;
            }
        }

        Ok(op_id)
    }

    /// Close a TCP stream
    pub fn tcp_close(&mut self, stream_id: i64) -> bool {
        self.tcp_streams.remove(stream_id).is_some()
    }

    /// Close a TCP listener
    pub fn tcp_listener_close(&mut self, listener_id: i64) -> bool {
        self.tcp_listeners.remove(listener_id).is_some()
    }

    // ========================================================================
    // UDP Operations
    // ========================================================================

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
    ) -> Result<u64, String> {
        if !self.udp_sockets.is_available(socket_id) {
            return Err("Invalid socket ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::with_handle(op_id, OpType::UdpSendTo, future_ptr, socket_id);
        op.data = Some(data);
        op.addr = Some(addr.to_string());
        self.pending.insert(op_id, op);

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = socket_id;
            }
        }

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
        if !self.udp_sockets.is_available(socket_id) {
            return Err("Invalid socket ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::with_handle(op_id, OpType::UdpRecvFrom, future_ptr, socket_id);
        op.buffer = Some(buffer);
        op.max_len = max_len;
        self.pending.insert(op_id, op);

        unsafe {
            if !future_ptr.is_null() {
                (*future_ptr).io_handle = socket_id;
            }
        }

        Ok(op_id)
    }

    /// Close a UDP socket
    pub fn udp_close(&mut self, socket_id: i64) -> bool {
        self.udp_sockets.remove(socket_id).is_some()
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
        let mut taken_listeners: HashMap<i64, TcpListener> = HashMap::new();
        let mut taken_streams: HashMap<i64, TcpStream> = HashMap::new();
        let mut taken_sockets: HashMap<i64, UdpSocket> = HashMap::new();

        for (_, op_type, handle_id, _, _, _, _) in &op_data {
            match op_type {
                OpType::TcpAccept => {
                    if let Some(l) = self.tcp_listeners.take(*handle_id) {
                        taken_listeners.insert(*handle_id, l);
                    }
                }
                OpType::TcpRead | OpType::TcpWrite => {
                    if let Some(s) = self.tcp_streams.take(*handle_id) {
                        taken_streams.insert(*handle_id, s);
                    }
                }
                OpType::UdpRecvFrom | OpType::UdpSendTo => {
                    if let Some(s) = self.udp_sockets.take(*handle_id) {
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
                    let result = match op_type {
                        OpType::TcpAccept => {
                            let listener = listeners_clone.borrow_mut().remove(&handle_id);
                            match listener {
                                Some(l) => {
                                    let res = l.accept().await;
                                    listeners_clone.borrow_mut().insert(handle_id, l);
                                    match res {
                                        Ok((stream, _addr)) => {
                                            new_streams_clone.borrow_mut().push((op_id, stream));
                                            Ok(OpResult::Handle(0)) // Placeholder, will update
                                        }
                                        Err(e) => Err(format!("Accept failed: {}", e)),
                                    }
                                }
                                None => Err("Listener not available".to_string()),
                            }
                        }
                        OpType::TcpConnect => {
                            let addr_str = addr.unwrap_or_default();
                            match addr_str.parse::<SocketAddr>() {
                                Ok(socket_addr) => {
                                    match TcpStream::connect(socket_addr).await {
                                        Ok(stream) => {
                                            new_streams_clone.borrow_mut().push((op_id, stream));
                                            Ok(OpResult::Handle(0)) // Placeholder
                                        }
                                        Err(e) => Err(format!("Connect failed: {}", e)),
                                    }
                                }
                                Err(e) => Err(format!("Invalid address: {}", e)),
                            }
                        }
                        OpType::TcpRead => {
                            let stream = streams_clone.borrow_mut().remove(&handle_id);
                            match stream {
                                Some(mut s) => {
                                    let buf = OwnedBuf::new(max_len);
                                    let (res, buf) = s.read(buf).await;
                                    streams_clone.borrow_mut().insert(handle_id, s);
                                    match res {
                                        Ok(n) => Ok(OpResult::Data(buf.into_vec()[..n].to_vec())),
                                        Err(e) => Err(format!("Read failed: {}", e)),
                                    }
                                }
                                None => Err("Stream not available".to_string()),
                            }
                        }
                        OpType::TcpWrite => {
                            let stream = streams_clone.borrow_mut().remove(&handle_id);
                            let write_data = data.unwrap_or_default();
                            match stream {
                                Some(mut s) => {
                                    let (res, _) = s.write(write_data).await;
                                    streams_clone.borrow_mut().insert(handle_id, s);
                                    match res {
                                        Ok(n) => Ok(OpResult::Bytes(n)),
                                        Err(e) => Err(format!("Write failed: {}", e)),
                                    }
                                }
                                None => Err("Stream not available".to_string()),
                            }
                        }
                        OpType::UdpRecvFrom => {
                            let socket = sockets_clone.borrow_mut().remove(&handle_id);
                            match socket {
                                Some(s) => {
                                    let buf = OwnedBuf::new(max_len);
                                    let (res, buf) = s.recv_from(buf).await;
                                    sockets_clone.borrow_mut().insert(handle_id, s);
                                    match res {
                                        Ok((n, addr)) => Ok(OpResult::DataFrom(buf.into_vec()[..n].to_vec(), addr)),
                                        Err(e) => Err(format!("RecvFrom failed: {}", e)),
                                    }
                                }
                                None => Err("Socket not available".to_string()),
                            }
                        }
                        OpType::UdpSendTo => {
                            let socket = sockets_clone.borrow_mut().remove(&handle_id);
                            let send_data = data.unwrap_or_default();
                            let addr_str = addr.unwrap_or_default();
                            match socket {
                                Some(s) => match addr_str.parse::<SocketAddr>() {
                                    Ok(socket_addr) => {
                                        let (res, _) = s.send_to(send_data, socket_addr).await;
                                        sockets_clone.borrow_mut().insert(handle_id, s);
                                        match res {
                                            Ok(n) => Ok(OpResult::Bytes(n)),
                                            Err(e) => Err(format!("SendTo failed: {}", e)),
                                        }
                                    }
                                    Err(e) => {
                                        sockets_clone.borrow_mut().insert(handle_id, s);
                                        Err(format!("Invalid address: {}", e))
                                    }
                                },
                                None => Err("Socket not available".to_string()),
                            }
                        }
                    };

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
            self.tcp_listeners.put_back(id, listener);
        }
        for (id, stream) in streams.borrow_mut().drain() {
            self.tcp_streams.put_back(id, stream);
        }
        for (id, socket) in sockets.borrow_mut().drain() {
            self.udp_sockets.put_back(id, socket);
        }

        // Process new streams from accept/connect
        let mut stream_ids: HashMap<u64, i64> = HashMap::new();
        for (op_id, stream) in new_streams.borrow_mut().drain(..) {
            let stream_id = self.tcp_streams.insert(stream);
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
        (self.tcp_streams.len(), self.tcp_listeners.len(), self.udp_sockets.len())
    }
}

impl Default for AsyncExecutor {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Thread-Local Executor
// ============================================================================

thread_local! {
    static EXECUTOR: RefCell<AsyncExecutor> = RefCell::new(AsyncExecutor::new());
}

/// Access the thread-local executor
pub fn with_executor<F, R>(f: F) -> R
where
    F: FnOnce(&mut AsyncExecutor) -> R,
{
    EXECUTOR.with(|exec| f(&mut exec.borrow_mut()))
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Initialize the async executor
#[no_mangle]
pub extern "C" fn rt_monoio_async_init(entries: i64) -> RuntimeValue {
    let entries = if entries < 1 || entries > 32768 {
        256
    } else {
        entries as u32
    };

    with_executor(|exec| {
        exec.init(entries);
    });

    RuntimeValue::from_int(1)
}

/// Submit an async TCP accept operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_accept(listener_handle: RuntimeValue, future: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_accept_submit(listener_id, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_accept: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP connect operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_connect(addr: RuntimeValue, future: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_tcp_connect: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_connect_submit(&addr_str, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_connect: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP read operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_read(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    max_len: i64,
    future: RuntimeValue,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_read_submit(stream_id, buffer, max_len as usize, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_read: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Submit an async TCP write operation (non-blocking)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_write(
    stream_handle: RuntimeValue,
    buffer: RuntimeValue,
    len: i64,
    future: RuntimeValue,
) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    // Extract data from buffer
    let data = match crate::monoio_runtime::extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_async_tcp_write: Invalid buffer");
            return RuntimeValue::from_int(-1);
        }
    };

    let future_ptr = if future.is_heap() {
        let ptr = future.as_heap_ptr();
        unsafe {
            if (*ptr).object_type == HeapObjectType::MonoioFuture {
                ptr as *mut MonoioFuture
            } else {
                std::ptr::null_mut()
            }
        }
    } else {
        std::ptr::null_mut()
    };

    let result = with_executor(|exec| exec.tcp_write_submit(stream_id, data, future_ptr));

    match result {
        Ok(op_id) => RuntimeValue::from_int(op_id as i64),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_write: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Poll all pending operations
#[no_mangle]
pub extern "C" fn rt_monoio_async_poll_all() -> RuntimeValue {
    let completed = with_executor(|exec| exec.poll_all());
    RuntimeValue::from_int(completed as i64)
}

/// Poll a single operation by ID
#[no_mangle]
pub extern "C" fn rt_monoio_async_poll_one(op_id: i64) -> RuntimeValue {
    let completed = with_executor(|exec| exec.poll_one(op_id as u64));
    RuntimeValue::from_bool(completed)
}

/// Get the number of pending operations
#[no_mangle]
pub extern "C" fn rt_monoio_async_pending_count() -> RuntimeValue {
    let count = with_executor(|exec| exec.pending_count());
    RuntimeValue::from_int(count as i64)
}

/// TCP listen (synchronous, returns handle)
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_tcp_listen: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = with_executor(|exec| exec.tcp_listen(&addr_str));

    match result {
        Ok(id) => RuntimeValue::from_int(id),
        Err(e) => {
            tracing::error!("rt_monoio_async_tcp_listen: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP stream
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();
    let success = with_executor(|exec| exec.tcp_close(stream_id));
    RuntimeValue::from_bool(success)
}

/// Close a TCP listener
#[no_mangle]
pub extern "C" fn rt_monoio_async_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();
    let success = with_executor(|exec| exec.tcp_listener_close(listener_id));
    RuntimeValue::from_bool(success)
}

/// UDP bind (synchronous, returns handle)
#[no_mangle]
pub extern "C" fn rt_monoio_async_udp_bind(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_async_udp_bind: Invalid address");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = with_executor(|exec| exec.udp_bind(&addr_str));

    match result {
        Ok(id) => RuntimeValue::from_int(id),
        Err(e) => {
            tracing::error!("rt_monoio_async_udp_bind: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a UDP socket
#[no_mangle]
pub extern "C" fn rt_monoio_async_udp_close(socket_handle: RuntimeValue) -> RuntimeValue {
    let socket_id = socket_handle.as_int();
    let success = with_executor(|exec| exec.udp_close(socket_id));
    RuntimeValue::from_bool(success)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_store() {
        let mut store: HandleStore<i32> = HandleStore::new();

        let id1 = store.insert(100);
        let id2 = store.insert(200);

        assert_eq!(id1, 1);
        assert_eq!(id2, 2);
        assert_eq!(store.get(id1), Some(&100));
        assert_eq!(store.get(id2), Some(&200));

        // Take and put back
        let val = store.take(id1);
        assert_eq!(val, Some(100));
        assert!(!store.is_available(id1));

        store.put_back(id1, 150);
        assert!(store.is_available(id1));
        assert_eq!(store.get(id1), Some(&150));

        // Remove
        store.remove(id2);
        assert!(!store.is_available(id2));
    }

    #[test]
    fn test_executor_init() {
        with_executor(|exec| {
            exec.init(256);
            assert!(exec.is_initialized());
        });
    }

    #[test]
    fn test_pending_count() {
        with_executor(|exec| {
            assert_eq!(exec.pending_count(), 0);
        });
    }
}
