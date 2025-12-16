//! Channel operations and FFI functions.
//!
//! Channels provide multi-producer, single-consumer communication between
//! actors or async tasks.

use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

// ============================================================================
// Channel Types
// ============================================================================

/// A channel sender (can be cloned for multiple producers)
#[repr(C)]
pub struct RuntimeChannelSender {
    pub header: HeapHeader,
    /// Sender handle (boxed Arc<Mutex<Sender>>)
    pub sender: *mut Arc<Mutex<Sender<RuntimeValue>>>,
    /// Channel ID for identification
    pub channel_id: u64,
}

/// A channel receiver (single consumer)
#[repr(C)]
pub struct RuntimeChannelReceiver {
    pub header: HeapHeader,
    /// Receiver handle (boxed Arc<Mutex<Receiver>>)
    pub receiver: *mut Arc<Mutex<Receiver<RuntimeValue>>>,
    /// Channel ID for identification
    pub channel_id: u64,
    /// Closed flag
    pub closed: u8,
}

/// A channel pair (sender + receiver bundled together)
#[repr(C)]
pub struct RuntimeChannel {
    pub header: HeapHeader,
    /// Sender handle
    pub sender: *mut Arc<Mutex<Sender<RuntimeValue>>>,
    /// Receiver handle
    pub receiver: *mut Arc<Mutex<Receiver<RuntimeValue>>>,
    /// Channel ID
    pub channel_id: u64,
    /// Closed flag
    pub closed: u8,
    /// Reserved for alignment
    pub reserved: [u8; 7],
}

// Track channel IDs
use std::sync::atomic::{AtomicU64, Ordering};
static NEXT_CHANNEL_ID: AtomicU64 = AtomicU64::new(1);

// ============================================================================
// Channel FFI Functions
// ============================================================================

/// Create a new channel. Returns a channel pair with sender and receiver.
#[no_mangle]
pub extern "C" fn rt_channel_new() -> RuntimeValue {
    let (tx, rx) = mpsc::channel::<RuntimeValue>();
    let channel_id = NEXT_CHANNEL_ID.fetch_add(1, Ordering::SeqCst);

    let sender = Box::into_raw(Box::new(Arc::new(Mutex::new(tx))));
    let receiver = Box::into_raw(Box::new(Arc::new(Mutex::new(rx))));

    let size = std::mem::size_of::<RuntimeChannel>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeChannel;
        if ptr.is_null() {
            // Clean up on allocation failure
            drop(Box::from_raw(sender));
            drop(Box::from_raw(receiver));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Channel, size as u32);
        (*ptr).sender = sender;
        (*ptr).receiver = receiver;
        (*ptr).channel_id = channel_id;
        (*ptr).closed = 0;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Helper to validate channel pointer
fn as_channel_ptr(value: RuntimeValue) -> Option<*mut RuntimeChannel> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Channel {
            return None;
        }
        Some(ptr as *mut RuntimeChannel)
    }
}

/// Send a value through the channel.
/// Returns 1 on success, 0 on failure (channel closed or disconnected).
#[no_mangle]
pub extern "C" fn rt_channel_send(channel: RuntimeValue, value: RuntimeValue) -> i64 {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return 0;
    };

    unsafe {
        if (*ch_ptr).closed != 0 || (*ch_ptr).sender.is_null() {
            return 0;
        }

        let sender = &*(*ch_ptr).sender;
        match sender.lock() {
            Ok(guard) => {
                if guard.send(value).is_ok() {
                    1
                } else {
                    0
                }
            }
            Err(_) => 0,
        }
    }
}

/// Receive a value from the channel (blocking with timeout).
/// Returns the received value, or NIL if the channel is closed/empty after timeout.
#[no_mangle]
pub extern "C" fn rt_channel_recv(channel: RuntimeValue) -> RuntimeValue {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        if (*ch_ptr).closed != 0 || (*ch_ptr).receiver.is_null() {
            return RuntimeValue::NIL;
        }

        let receiver = &*(*ch_ptr).receiver;
        match receiver.lock() {
            Ok(guard) => {
                // Use timeout to avoid blocking forever
                match guard.recv_timeout(Duration::from_secs(30)) {
                    Ok(val) => val,
                    Err(_) => RuntimeValue::NIL,
                }
            }
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Try to receive a value from the channel without blocking.
/// Returns the received value, or NIL if no value is available.
#[no_mangle]
pub extern "C" fn rt_channel_try_recv(channel: RuntimeValue) -> RuntimeValue {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        if (*ch_ptr).closed != 0 || (*ch_ptr).receiver.is_null() {
            return RuntimeValue::NIL;
        }

        let receiver = &*(*ch_ptr).receiver;
        match receiver.lock() {
            Ok(guard) => match guard.try_recv() {
                Ok(val) => val,
                Err(TryRecvError::Empty) => RuntimeValue::NIL,
                Err(TryRecvError::Disconnected) => RuntimeValue::NIL,
            },
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Receive a value with a timeout in milliseconds.
/// Returns the received value, or NIL if timeout expires.
#[no_mangle]
pub extern "C" fn rt_channel_recv_timeout(channel: RuntimeValue, timeout_ms: i64) -> RuntimeValue {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return RuntimeValue::NIL;
    };

    let timeout = if timeout_ms <= 0 {
        Duration::from_millis(1)
    } else {
        Duration::from_millis(timeout_ms as u64)
    };

    unsafe {
        if (*ch_ptr).closed != 0 || (*ch_ptr).receiver.is_null() {
            return RuntimeValue::NIL;
        }

        let receiver = &*(*ch_ptr).receiver;
        match receiver.lock() {
            Ok(guard) => match guard.recv_timeout(timeout) {
                Ok(val) => val,
                Err(_) => RuntimeValue::NIL,
            },
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Close the channel. No more values can be sent after closing.
#[no_mangle]
pub extern "C" fn rt_channel_close(channel: RuntimeValue) {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return;
    };

    unsafe {
        (*ch_ptr).closed = 1;
        // Drop the sender to signal disconnection
        if !(*ch_ptr).sender.is_null() {
            drop(Box::from_raw((*ch_ptr).sender));
            (*ch_ptr).sender = std::ptr::null_mut();
        }
    }
}

/// Check if the channel is closed.
/// Returns 1 if closed, 0 if open.
#[no_mangle]
pub extern "C" fn rt_channel_is_closed(channel: RuntimeValue) -> i64 {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return 1;
    };

    unsafe {
        if (*ch_ptr).closed != 0 { 1 } else { 0 }
    }
}

/// Get the channel ID.
#[no_mangle]
pub extern "C" fn rt_channel_id(channel: RuntimeValue) -> i64 {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return 0;
    };

    unsafe { (*ch_ptr).channel_id as i64 }
}

/// Free a channel and its resources.
#[no_mangle]
pub extern "C" fn rt_channel_free(channel: RuntimeValue) {
    let Some(ch_ptr) = as_channel_ptr(channel) else {
        return;
    };

    unsafe {
        // Free sender if not already freed
        if !(*ch_ptr).sender.is_null() {
            drop(Box::from_raw((*ch_ptr).sender));
        }
        // Free receiver
        if !(*ch_ptr).receiver.is_null() {
            drop(Box::from_raw((*ch_ptr).receiver));
        }

        let size = std::mem::size_of::<RuntimeChannel>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(ch_ptr as *mut u8, layout);
    }
}

// ============================================================================
// Unit Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_channel_new() {
        let ch = rt_channel_new();
        assert!(ch.is_heap());
        assert_eq!(rt_channel_is_closed(ch), 0);
        assert!(rt_channel_id(ch) > 0);
        rt_channel_free(ch);
    }

    #[test]
    fn test_channel_send_recv() {
        let ch = rt_channel_new();

        // Send a value
        let val = RuntimeValue::from_int(42);
        let result = rt_channel_send(ch, val);
        assert_eq!(result, 1);

        // Receive the value
        let received = rt_channel_try_recv(ch);
        assert!(received.is_int());
        assert_eq!(received.as_int(), 42);

        rt_channel_free(ch);
    }

    #[test]
    fn test_channel_try_recv_empty() {
        let ch = rt_channel_new();

        // Try to receive from empty channel
        let received = rt_channel_try_recv(ch);
        assert!(received.is_nil());

        rt_channel_free(ch);
    }

    #[test]
    fn test_channel_close() {
        let ch = rt_channel_new();

        // Close the channel
        rt_channel_close(ch);
        assert_eq!(rt_channel_is_closed(ch), 1);

        // Send should fail after close
        let val = RuntimeValue::from_int(42);
        let result = rt_channel_send(ch, val);
        assert_eq!(result, 0);

        rt_channel_free(ch);
    }

    #[test]
    fn test_channel_multiple_values() {
        let ch = rt_channel_new();

        // Send multiple values
        for i in 0..5 {
            let val = RuntimeValue::from_int(i);
            assert_eq!(rt_channel_send(ch, val), 1);
        }

        // Receive all values in order
        for i in 0..5 {
            let received = rt_channel_try_recv(ch);
            assert!(received.is_int());
            assert_eq!(received.as_int(), i);
        }

        rt_channel_free(ch);
    }
}
