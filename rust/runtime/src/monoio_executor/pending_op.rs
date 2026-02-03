// Pending Operation tracking for async I/O
// Manages state for individual async operations and their futures.

#![cfg(feature = "monoio-direct")]

use crate::value::monoio_future::{MonoioFuture, FUTURE_STATE_ERROR, FUTURE_STATE_READY};
use crate::value::RuntimeValue;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::types::{OpResult, OpState, OpType};

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pending_op_new() {
        let op = PendingOp::new(1, OpType::TcpConnect, std::ptr::null_mut());
        assert_eq!(op.id, 1);
        assert_eq!(op.op_type, OpType::TcpConnect);
        assert!(matches!(op.state, OpState::NotStarted));
    }

    #[test]
    fn test_pending_op_with_handle() {
        let op = PendingOp::with_handle(2, OpType::TcpRead, std::ptr::null_mut(), 42);
        assert_eq!(op.id, 2);
        assert_eq!(op.handle_id, 42);
    }
}
