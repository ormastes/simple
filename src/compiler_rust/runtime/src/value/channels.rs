//! Channel operations and SFFI functions.
//!
//! Channels provide multi-producer, single-consumer communication between
//! actors or async tasks.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver, SyncSender, TryRecvError};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use super::core::RuntimeValue;
use super::heap::{register_heap_ptr, unregister_heap_ptr_checked, with_typed_ptr, HeapHeader, HeapObjectType};
use super::transfer::{RuntimeEncodedCopy, RuntimeTransferPacket, TransferDomain};

const DEFAULT_CHANNEL_CAPACITY: usize = 256;

// ============================================================================
// Channel Types
// ============================================================================

/// One admitted channel message.
///
/// Inline scalars travel as a 48-byte inline packet; heap leaves (text,
/// boxed numeric scalars) travel as a schema-checked encoded copy so no
/// process-local heap address ever crosses the thread boundary. Refused
/// or malformed packets never enter the queue — send fails closed with 0.
enum RuntimeChannelPacket {
    Inline(RuntimeTransferPacket),
    Encoded(RuntimeEncodedCopy),
}

impl RuntimeChannelPacket {
    /// Decode this packet for a receiver in `target` domain.
    fn into_runtime_value_for_target(self, target: TransferDomain) -> Option<RuntimeValue> {
        match self {
            RuntimeChannelPacket::Inline(packet) => packet.runtime_value_for_target(target),
            RuntimeChannelPacket::Encoded(copy) => copy.materialize_for_target(target),
        }
    }
}

/// Admit one value into a channel packet: inline scalars first, then
/// encoded heap leaves. Returns `None` for non-transferable values
/// (mutable containers, unknown heap identity), so the send fails closed.
fn channel_packet_for_value(value: RuntimeValue) -> Option<RuntimeChannelPacket> {
    RuntimeTransferPacket::inline_copy(value, TransferDomain::Parent, TransferDomain::Thread)
        .map(RuntimeChannelPacket::Inline)
        .or_else(|| {
            RuntimeEncodedCopy::from_value(value, TransferDomain::Parent, TransferDomain::Thread)
                .map(RuntimeChannelPacket::Encoded)
        })
}

struct RuntimeChannelState {
    sender: Mutex<Option<SyncSender<RuntimeChannelPacket>>>,
    receiver: Mutex<Receiver<RuntimeChannelPacket>>,
    closed: AtomicBool,
}

/// A channel pair (sender + receiver bundled together).
///
/// The heap object owns one boxed `Arc`; operations clone that `Arc` while the
/// heap-allocation registry is locked. A concurrent free can therefore remove
/// the handle without invalidating an operation that already acquired state.
#[repr(C)]
pub struct RuntimeChannel {
    pub header: HeapHeader,
    state: *mut Arc<RuntimeChannelState>,
    /// Channel ID
    pub channel_id: u64,
}

// Track channel IDs
static NEXT_CHANNEL_ID: AtomicU64 = AtomicU64::new(1);

// ============================================================================
// Channel SFFI Functions
// ============================================================================

/// Create a new channel. Returns a channel pair with sender and receiver.
#[no_mangle]
pub extern "C" fn rt_channel_new() -> RuntimeValue {
    let (tx, rx) = mpsc::sync_channel::<RuntimeChannelPacket>(DEFAULT_CHANNEL_CAPACITY);
    let channel_id = NEXT_CHANNEL_ID.fetch_add(1, Ordering::SeqCst);

    let state = Box::into_raw(Box::new(Arc::new(RuntimeChannelState {
        sender: Mutex::new(Some(tx)),
        receiver: Mutex::new(rx),
        closed: AtomicBool::new(false),
    })));

    let size = std::mem::size_of::<RuntimeChannel>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeChannel;
        if ptr.is_null() {
            // Clean up on allocation failure
            drop(Box::from_raw(state));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Channel, size as u32);
        (*ptr).state = state;
        (*ptr).channel_id = channel_id;

        register_heap_ptr(ptr as *mut HeapHeader);
        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn channel_state(value: RuntimeValue) -> Option<(Arc<RuntimeChannelState>, u64)> {
    with_typed_ptr::<RuntimeChannel, _>(value, HeapObjectType::Channel, |ptr| unsafe {
        let state = (*ptr).state;
        (!state.is_null()).then(|| ((&*state).clone(), (*ptr).channel_id))
    })?
}

/// Send a value through the channel.
/// Returns 1 on success, 0 when full, closed, disconnected, or non-transferable.
#[no_mangle]
pub extern "C" fn rt_channel_send(channel: RuntimeValue, value: RuntimeValue) -> i64 {
    let Some((state, _)) = channel_state(channel) else {
        return 0;
    };
    // The legacy channel API has no endpoint-role metadata. Until typed channel
    // endpoints land, its admitted compatibility route is parent -> thread.
    // Text and boxed numeric leaves travel as an encoded copy; every other
    // non-transferable value is refused (returns 0) rather than silently
    // dropped, so callers can tell admission from loss.
    let Some(packet) = channel_packet_for_value(value) else {
        return 0;
    };

    if state.closed.load(Ordering::Acquire) {
        return 0;
    }
    let result = match state.sender.lock() {
        Ok(guard) => match guard.as_ref() {
            Some(sender) if sender.try_send(packet).is_ok() => 1,
            _ => 0,
        },
        Err(_) => 0,
    };
    result
}

/// Receive a value from the channel (blocking with timeout).
/// Returns the received value, or NIL if the channel is closed/empty after timeout.
#[no_mangle]
pub extern "C" fn rt_channel_recv(channel: RuntimeValue) -> RuntimeValue {
    let Some((state, _)) = channel_state(channel) else {
        return RuntimeValue::NIL;
    };

    if state.closed.load(Ordering::Acquire) {
        return RuntimeValue::NIL;
    }
    let result = match state.receiver.lock() {
        Ok(guard) => match guard.recv_timeout(Duration::from_secs(30)) {
            Ok(packet) => packet
                .into_runtime_value_for_target(TransferDomain::Thread)
                .unwrap_or(RuntimeValue::NIL),
            Err(_) => RuntimeValue::NIL,
        },
        Err(_) => RuntimeValue::NIL,
    };
    result
}

/// Try to receive a value from the channel without blocking.
/// Returns the received value, or NIL if no value is available.
#[no_mangle]
pub extern "C" fn rt_channel_try_recv(channel: RuntimeValue) -> RuntimeValue {
    let Some((state, _)) = channel_state(channel) else {
        return RuntimeValue::NIL;
    };

    if state.closed.load(Ordering::Acquire) {
        return RuntimeValue::NIL;
    }
    let result = match state.receiver.lock() {
        Ok(guard) => match guard.try_recv() {
            Ok(packet) => packet
                .into_runtime_value_for_target(TransferDomain::Thread)
                .unwrap_or(RuntimeValue::NIL),
            Err(TryRecvError::Empty) => RuntimeValue::NIL,
            Err(TryRecvError::Disconnected) => RuntimeValue::NIL,
        },
        Err(_) => RuntimeValue::NIL,
    };
    result
}

/// Receive a value with a timeout in milliseconds.
/// Returns the received value, or NIL if timeout expires.
#[no_mangle]
pub extern "C" fn rt_channel_recv_timeout(channel: RuntimeValue, timeout_ms: i64) -> RuntimeValue {
    let Some((state, _)) = channel_state(channel) else {
        return RuntimeValue::NIL;
    };

    let timeout = if timeout_ms <= 0 {
        Duration::from_millis(1)
    } else {
        Duration::from_millis(timeout_ms as u64)
    };

    if state.closed.load(Ordering::Acquire) {
        return RuntimeValue::NIL;
    }
    let result = match state.receiver.lock() {
        Ok(guard) => match guard.recv_timeout(timeout) {
            Ok(packet) => packet
                .into_runtime_value_for_target(TransferDomain::Thread)
                .unwrap_or(RuntimeValue::NIL),
            Err(_) => RuntimeValue::NIL,
        },
        Err(_) => RuntimeValue::NIL,
    };
    result
}

/// Close the channel. No more values can be sent after closing.
#[no_mangle]
pub extern "C" fn rt_channel_close(channel: RuntimeValue) {
    let Some((state, _)) = channel_state(channel) else {
        return;
    };
    state.closed.store(true, Ordering::Release);
    if let Ok(mut sender) = state.sender.lock() {
        sender.take();
    };
}

/// Check if the channel is closed.
/// Returns 1 if closed, 0 if open.
#[no_mangle]
pub extern "C" fn rt_channel_is_closed(channel: RuntimeValue) -> i64 {
    let Some((state, _)) = channel_state(channel) else {
        return 1;
    };
    i64::from(state.closed.load(Ordering::Acquire))
}

/// Get the channel ID.
#[no_mangle]
pub extern "C" fn rt_channel_id(channel: RuntimeValue) -> i64 {
    let Some((_, channel_id)) = channel_state(channel) else {
        return 0;
    };
    channel_id as i64
}

/// Free a channel and its resources.
#[no_mangle]
pub extern "C" fn rt_channel_free(channel: RuntimeValue) {
    if !channel.is_heap() {
        return;
    }
    let ch_ptr = channel.as_heap_ptr() as *mut RuntimeChannel;
    if !unregister_heap_ptr_checked(ch_ptr as *mut HeapHeader) {
        return;
    }

    unsafe {
        if !(*ch_ptr).state.is_null() {
            drop(Box::from_raw((*ch_ptr).state));
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
    use crate::value::heap::{with_typed_ptr, HeapObjectType};
    use crate::value::{rt_array_free, rt_array_new, rt_string_new};
    use std::sync::Barrier;
    use std::thread;

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

    #[test]
    fn test_channel_rejects_forged_heap_value() {
        let forged_heap = RuntimeValue::from_raw(0x1001);

        assert_eq!(rt_channel_send(forged_heap, RuntimeValue::from_int(1)), 0);
        assert_eq!(rt_channel_recv(forged_heap), RuntimeValue::NIL);
        assert_eq!(rt_channel_try_recv(forged_heap), RuntimeValue::NIL);
        assert_eq!(rt_channel_recv_timeout(forged_heap, 1), RuntimeValue::NIL);
        assert_eq!(rt_channel_is_closed(forged_heap), 1);
        assert_eq!(rt_channel_id(forged_heap), 0);
        rt_channel_close(forged_heap);
        rt_channel_free(forged_heap);
    }

    #[test]
    fn test_channel_rejects_heap_tagged_payload() {
        let ch = rt_channel_new();
        let process_local_pointer = RuntimeValue::from_raw(0x1001);

        assert!(!process_local_pointer.is_inline_transfer_value());
        assert_eq!(rt_channel_send(ch, process_local_pointer), 0);
        assert_eq!(rt_channel_send(ch, RuntimeValue::from_raw(0x1004)), 0);
        assert_eq!(rt_channel_try_recv(ch), RuntimeValue::NIL);

        rt_channel_free(ch);
    }

    #[test]
    fn test_deep_copy_fails_closed_for_mutable_heap_graph() {
        let array = rt_array_new(1);
        assert!(array.is_heap());
        assert_eq!(array.deep_copy(), RuntimeValue::NIL);
        rt_array_free(array);
    }

    #[test]
    fn test_channel_has_finite_default_capacity() {
        let ch = rt_channel_new();
        for i in 0..DEFAULT_CHANNEL_CAPACITY {
            assert_eq!(rt_channel_send(ch, RuntimeValue::from_int(i as i64)), 1);
        }
        assert_eq!(rt_channel_send(ch, RuntimeValue::from_int(999)), 0);

        rt_channel_free(ch);
    }

    #[test]
    fn acquired_channel_state_outlives_handle_free() {
        let ch = rt_channel_new();
        let (state, channel_id) = channel_state(ch).unwrap();

        rt_channel_free(ch);
        assert_eq!(rt_channel_id(ch), 0);
        assert!(channel_id > 0);

        let packet = RuntimeTransferPacket::inline_copy(
            RuntimeValue::from_int(42),
            TransferDomain::Parent,
            TransferDomain::Thread,
        )
        .unwrap();
        state.sender.lock().unwrap().as_ref().unwrap().try_send(RuntimeChannelPacket::Inline(packet)).unwrap();
        let received = state.receiver.lock().unwrap().try_recv().unwrap();
        assert_eq!(
            received
                .into_runtime_value_for_target(TransferDomain::Thread)
                .unwrap()
                .as_int(),
            42
        );
    }

    #[test]
    fn test_channel_send_recv_text_same_thread() {
        let ch = rt_channel_new();
        let text = rt_string_new(b"hello-channel-text".as_ptr(), 18);
        assert_eq!(rt_channel_send(ch, text), 1);

        let received = rt_channel_try_recv(ch);
        assert!(received.is_heap());
        let round_tripped = with_typed_ptr::<crate::value::collections::RuntimeString, _>(
            received,
            HeapObjectType::String,
            |ptr| unsafe { (*ptr).as_bytes().to_vec() },
        )
        .expect("received value is a string");
        assert_eq!(round_tripped, b"hello-channel-text");

        rt_channel_free(ch);
    }

    #[test]
    fn test_channel_cross_thread_text_and_i64() {
        let ch = rt_channel_new();

        let worker = thread::spawn(move || {
            // Literal-shaped sends from the child: text via the encoded-copy
            // route, i64 via the inline route.
            assert_eq!(rt_channel_send(ch, RuntimeValue::from_int(77)), 1);
            let text = rt_string_new(b"child-text".as_ptr(), 10);
            assert_eq!(rt_channel_send(ch, text), 1);
        });

        let first = rt_channel_recv_timeout(ch, 5_000);
        assert!(first.is_int());
        assert_eq!(first.as_int(), 77);

        let second = rt_channel_recv_timeout(ch, 5_000);
        assert!(second.is_heap());
        let bytes = with_typed_ptr::<crate::value::collections::RuntimeString, _>(
            second,
            HeapObjectType::String,
            |ptr| unsafe { (*ptr).as_bytes().to_vec() },
        )
        .expect("received value is a string");
        assert_eq!(bytes, b"child-text");

        worker.join().unwrap();
        rt_channel_free(ch);
    }

    #[test]
    fn concurrent_send_close_and_free_fail_closed() {
        let ch = rt_channel_new();
        let raw = ch.to_raw();
        let start = Arc::new(Barrier::new(3));

        let send_start = start.clone();
        let sender = thread::spawn(move || {
            let channel = RuntimeValue::from_raw(raw);
            send_start.wait();
            for value in 0..1_000 {
                let _ = rt_channel_send(channel, RuntimeValue::from_int(value));
            }
        });

        let close_start = start.clone();
        let closer = thread::spawn(move || {
            let channel = RuntimeValue::from_raw(raw);
            close_start.wait();
            rt_channel_close(channel);
        });

        start.wait();
        rt_channel_free(ch);
        sender.join().unwrap();
        closer.join().unwrap();

        assert_eq!(rt_channel_send(ch, RuntimeValue::from_int(1)), 0);
        assert_eq!(rt_channel_is_closed(ch), 1);
        rt_channel_free(ch);
    }
}
