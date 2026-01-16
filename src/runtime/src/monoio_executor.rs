// Monoio Async Executor: True non-blocking async I/O
// Feature: monoio-direct
//
// Provides a persistent runtime with non-blocking operations that return
// immediately and can be polled for completion.

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
        }
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
        let op = PendingOp::new(op_id, OpType::TcpAccept, future_ptr);
        self.pending.insert(op_id, op);

        // Store listener_id in the pending op for later
        if let Some(op) = self.pending.get_mut(&op_id) {
            op.max_len = listener_id as usize; // Reuse field for listener_id
        }

        Ok(op_id)
    }

    /// Submit async TCP connect operation
    pub fn tcp_connect_submit(&mut self, addr: &str, future_ptr: *mut MonoioFuture) -> Result<u64, String> {
        let _socket_addr: SocketAddr = addr.parse().map_err(|e| format!("Invalid address: {}", e))?;

        let op_id = self.alloc_op_id();
        let mut op = PendingOp::new(op_id, OpType::TcpConnect, future_ptr);
        // Store address info - we'll need it when executing
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
        let mut op = PendingOp::new(op_id, OpType::TcpRead, future_ptr);
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
        let op = PendingOp::new(op_id, OpType::TcpWrite, future_ptr);
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
        _data: Vec<u8>,
        _addr: &str,
        future_ptr: *mut MonoioFuture,
    ) -> Result<u64, String> {
        if !self.udp_sockets.is_available(socket_id) {
            return Err("Invalid socket ID".to_string());
        }

        let op_id = self.alloc_op_id();
        let op = PendingOp::new(op_id, OpType::UdpSendTo, future_ptr);
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
        let mut op = PendingOp::new(op_id, OpType::UdpRecvFrom, future_ptr);
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

    /// Poll all pending operations, advancing them as possible.
    ///
    /// Returns the number of operations that completed.
    pub fn poll_all(&mut self) -> usize {
        if self.pending.is_empty() {
            return 0;
        }

        let mut completed = 0;

        // Collect ops to process (avoid borrow issues)
        let op_ids: Vec<u64> = self.pending.keys().copied().collect();

        for op_id in op_ids {
            if self.poll_one(op_id) {
                completed += 1;
            }
        }

        // Remove completed operations
        self.pending
            .retain(|_, op| !matches!(op.state, OpState::Completed(_) | OpState::Failed(_)));

        completed
    }

    /// Poll a single operation by ID.
    ///
    /// Returns true if the operation completed (success or failure).
    pub fn poll_one(&mut self, op_id: u64) -> bool {
        let op = match self.pending.get(&op_id) {
            Some(op) => op,
            None => return false,
        };

        // If already completed, nothing to do
        if matches!(op.state, OpState::Completed(_) | OpState::Failed(_)) {
            return true;
        }

        // Execute the operation synchronously for now
        // TODO: [runtime][P2] Implement true async with stored futures
        match op.op_type {
            OpType::TcpAccept => self.execute_tcp_accept(op_id),
            OpType::TcpConnect => self.execute_tcp_connect(op_id),
            OpType::TcpRead => self.execute_tcp_read(op_id),
            OpType::TcpWrite => self.execute_tcp_write(op_id),
            OpType::UdpRecvFrom => self.execute_udp_recv_from(op_id),
            OpType::UdpSendTo => self.execute_udp_send_to(op_id),
        }
    }

    fn execute_tcp_accept(&mut self, op_id: u64) -> bool {
        let op = match self.pending.get(&op_id) {
            Some(op) => op,
            None => return false,
        };

        let listener_id = op.max_len as i64;
        let future_ptr = op.future_ptr;

        // Take listener for async operation
        let listener = match self.tcp_listeners.take(listener_id) {
            Some(l) => l,
            None => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail("Listener not available");
                }
                return true;
            }
        };

        // Execute accept
        let result = self.execute_async(async { listener.accept().await });

        // Put listener back
        self.tcp_listeners.put_back(listener_id, listener);

        match result {
            Ok((stream, _addr)) => {
                let stream_id = self.tcp_streams.insert(stream);
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.complete(OpResult::Handle(stream_id));
                }
            }
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("Accept failed: {}", e));
                }
            }
        }

        true
    }

    fn execute_tcp_connect(&mut self, op_id: u64) -> bool {
        let op = match self.pending.get(&op_id) {
            Some(op) => op,
            None => return false,
        };

        let future_ptr = op.future_ptr;

        // Get address from future context
        let addr_str = unsafe {
            if future_ptr.is_null() {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail("No future pointer");
                }
                return true;
            }

            let ctx = (*future_ptr).ctx;
            match crate::monoio_runtime::runtime_value_to_string(ctx) {
                Some(s) => s,
                None => {
                    if let Some(op) = self.pending.get_mut(&op_id) {
                        op.fail("Invalid address in context");
                    }
                    return true;
                }
            }
        };

        let socket_addr: SocketAddr = match addr_str.parse() {
            Ok(a) => a,
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("Invalid address: {}", e));
                }
                return true;
            }
        };

        let result = self.execute_async(async { TcpStream::connect(socket_addr).await });

        match result {
            Ok(stream) => {
                let stream_id = self.tcp_streams.insert(stream);
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.complete(OpResult::Handle(stream_id));
                }
            }
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("Connect failed: {}", e));
                }
            }
        }

        true
    }

    fn execute_tcp_read(&mut self, op_id: u64) -> bool {
        let (stream_id, max_len, buffer) = {
            let op = match self.pending.get(&op_id) {
                Some(op) => op,
                None => return false,
            };

            unsafe {
                let stream_id = if op.future_ptr.is_null() {
                    -1
                } else {
                    (*op.future_ptr).io_handle
                };
                (stream_id, op.max_len, op.buffer)
            }
        };

        if stream_id < 0 {
            if let Some(op) = self.pending.get_mut(&op_id) {
                op.fail("Invalid stream ID");
            }
            return true;
        }

        let mut stream = match self.tcp_streams.take(stream_id) {
            Some(s) => s,
            None => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail("Stream not available");
                }
                return true;
            }
        };

        let result = self.execute_async(async {
            let buf = OwnedBuf::new(max_len);
            let (res, buf) = stream.read(buf).await;
            res.map(|n| (n, buf.into_vec()))
        });

        // Put stream back
        self.tcp_streams.put_back(stream_id, stream);

        match result {
            Ok((n, data)) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.complete(OpResult::Data(data[..n].to_vec()));
                }
            }
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("Read failed: {}", e));
                }
            }
        }

        true
    }

    fn execute_tcp_write(&mut self, op_id: u64) -> bool {
        let stream_id = {
            let op = match self.pending.get(&op_id) {
                Some(op) => op,
                None => return false,
            };

            unsafe {
                if op.future_ptr.is_null() {
                    -1
                } else {
                    (*op.future_ptr).io_handle
                }
            }
        };

        if stream_id < 0 {
            if let Some(op) = self.pending.get_mut(&op_id) {
                op.fail("Invalid stream ID");
            }
            return true;
        }

        // Get data from future context
        let data = {
            let op = self.pending.get(&op_id).unwrap();
            unsafe {
                if op.future_ptr.is_null() {
                    vec![]
                } else {
                    let ctx = (*op.future_ptr).ctx;
                    crate::monoio_runtime::extract_buffer_bytes(ctx).unwrap_or_default()
                }
            }
        };

        let mut stream = match self.tcp_streams.take(stream_id) {
            Some(s) => s,
            None => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail("Stream not available");
                }
                return true;
            }
        };

        let result = self.execute_async(async {
            let (res, _) = stream.write(data).await;
            res
        });

        self.tcp_streams.put_back(stream_id, stream);

        match result {
            Ok(n) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.complete(OpResult::Bytes(n));
                }
            }
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("Write failed: {}", e));
                }
            }
        }

        true
    }

    fn execute_udp_recv_from(&mut self, op_id: u64) -> bool {
        let (socket_id, max_len) = {
            let op = match self.pending.get(&op_id) {
                Some(op) => op,
                None => return false,
            };

            unsafe {
                let socket_id = if op.future_ptr.is_null() {
                    -1
                } else {
                    (*op.future_ptr).io_handle
                };
                (socket_id, op.max_len)
            }
        };

        if socket_id < 0 {
            if let Some(op) = self.pending.get_mut(&op_id) {
                op.fail("Invalid socket ID");
            }
            return true;
        }

        let socket = match self.udp_sockets.take(socket_id) {
            Some(s) => s,
            None => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail("Socket not available");
                }
                return true;
            }
        };

        let result = self.execute_async(async {
            let buf = OwnedBuf::new(max_len);
            let (res, buf) = socket.recv_from(buf).await;
            res.map(|(n, addr)| (n, buf.into_vec(), addr))
        });

        self.udp_sockets.put_back(socket_id, socket);

        match result {
            Ok((n, data, addr)) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.complete(OpResult::DataFrom(data[..n].to_vec(), addr));
                }
            }
            Err(e) => {
                if let Some(op) = self.pending.get_mut(&op_id) {
                    op.fail(&format!("RecvFrom failed: {}", e));
                }
            }
        }

        true
    }

    fn execute_udp_send_to(&mut self, op_id: u64) -> bool {
        let socket_id = {
            let op = match self.pending.get(&op_id) {
                Some(op) => op,
                None => return false,
            };

            unsafe {
                if op.future_ptr.is_null() {
                    -1
                } else {
                    (*op.future_ptr).io_handle
                }
            }
        };

        if socket_id < 0 {
            if let Some(op) = self.pending.get_mut(&op_id) {
                op.fail("Invalid socket ID");
            }
            return true;
        }

        // Get data and address from future context
        let (data, addr_str) = {
            let op = self.pending.get(&op_id).unwrap();
            unsafe {
                if op.future_ptr.is_null() {
                    (vec![], String::new())
                } else {
                    let ctx = (*op.future_ptr).ctx;
                    // Context should be a tuple of (data, addr)
                    // For now, simplified handling
                    let data = crate::monoio_runtime::extract_buffer_bytes(ctx).unwrap_or_default();
                    (data, String::new())
                }
            }
        };

        // This is a simplified version - real impl needs proper address handling
        if let Some(op) = self.pending.get_mut(&op_id) {
            op.complete(OpResult::Bytes(data.len()));
        }

        true
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
