//! Actor operations and SFFI functions.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex, RwLock};
use std::time::Duration;

use super::core::RuntimeValue;
use super::heap::{get_typed_ptr_mut, HeapHeader, HeapObjectType};
use super::transfer::{RuntimeTransferPacket, TransferDomain};
use crate::concurrency::{spawn_actor, ActorHandle, Message};

thread_local! {
    pub(crate) static CURRENT_ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = const { RefCell::new(None) };
    pub(crate) static CURRENT_ACTOR_OUTBOX: RefCell<Option<mpsc::SyncSender<Message>>> = const { RefCell::new(None) };
}

// Global registry for ActorHandles (avoids storing Arc/Mutex in heap memory)
lazy_static::lazy_static! {
    static ref ACTOR_REGISTRY: Arc<RwLock<HashMap<usize, ActorHandle>>> =
        Arc::new(RwLock::new(HashMap::new()));
}

/// A heap-allocated actor reference (stores only the ID, not the full handle)
#[repr(C)]
pub struct RuntimeActor {
    pub header: HeapHeader,
    pub actor_id: usize,
}

fn alloc_actor(actor_id: usize) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeActor>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeActor;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Actor, size as u32);
        (*ptr).actor_id = actor_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_actor_ptr(value: RuntimeValue) -> Option<*mut RuntimeActor> {
    get_typed_ptr_mut::<RuntimeActor>(value, HeapObjectType::Actor)
}

fn get_actor_handle(actor_id: usize) -> Option<ActorHandle> {
    ACTOR_REGISTRY.read().ok()?.get(&actor_id).cloned()
}

fn encode_inline_actor_message(
    value: RuntimeValue,
    source_domain: TransferDomain,
    target_domain: TransferDomain,
) -> Option<Message> {
    let packet = RuntimeTransferPacket::inline_copy(value, source_domain, target_domain)?;
    Some(Message::TransferPacket(packet.encode()?))
}

fn decode_inline_actor_message(message: Message) -> Option<RuntimeValue> {
    let Message::TransferPacket(bytes) = message else {
        return None;
    };
    RuntimeTransferPacket::decode(&bytes)?.runtime_value_for_target(TransferDomain::Actor)
}

/// Spawn a new actor. `body_func` is a pointer to the actor body.
/// Returns a heap-allocated actor handle.
#[no_mangle]
pub extern "C" fn rt_actor_spawn(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    // Passing a heap context would donate a process-local pointer to another
    // execution domain. Reject it until actor construction accepts an owned or
    // encoded transfer packet.
    if ctx.is_heap() {
        return RuntimeValue::NIL;
    }
    // Interpret body_func as an extern "C" fn(ctx: *const u8) and run it inside the actor thread.
    // If body_func is 0, spawn a no-op actor that still owns a mailbox.
    let func: Option<extern "C" fn(*const u8)> = if body_func == 0 {
        None
    } else {
        Some(unsafe { std::mem::transmute::<usize, extern "C" fn(*const u8)>(body_func as usize) })
    };
    let handle = spawn_actor(move |inbox, outbox| {
        let inbox = Arc::new(Mutex::new(inbox));
        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));

        if let Some(f) = func {
            f(std::ptr::null());
        }

        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
    });

    let actor_id = handle.id();

    // Store handle in registry
    if let Ok(mut registry) = ACTOR_REGISTRY.write() {
        registry.insert(actor_id, handle);
    }

    alloc_actor(actor_id)
}

/// Try to send an inline runtime value to an actor.
/// Returns 1 only when the bounded actor inbox accepted the packet. Invalid
/// actors, heap/reserved values, full inboxes, and disconnected actors return 0.
#[no_mangle]
pub extern "C" fn rt_actor_try_send(actor: RuntimeValue, message: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe {
            let actor_id = (*actor_ptr).actor_id;
            if let Some(handle) = get_actor_handle(actor_id) {
                let source_domain = if CURRENT_ACTOR_INBOX.with(|cell| cell.borrow().is_some()) {
                    TransferDomain::Actor
                } else {
                    TransferDomain::Parent
                };
                if let Some(payload) = encode_inline_actor_message(message, source_domain, TransferDomain::Actor) {
                    return i64::from(handle.send(payload).is_ok());
                }
            }
        }
    }
    0
}

/// Legacy void send ABI retained for existing generated code.
#[no_mangle]
pub extern "C" fn rt_actor_send(actor: RuntimeValue, message: RuntimeValue) {
    let _ = rt_actor_try_send(actor, message);
}

/// Cooperatively stop an actor exactly once while preserving joinability.
/// Closing both retained sender owners wakes a blocked inbox receive; actor
/// code already executing outside receive remains cooperative.
#[no_mangle]
pub extern "C" fn rt_actor_stop(actor: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        let actor_id = unsafe { (*actor_ptr).actor_id };
        if let Some(handle) = get_actor_handle(actor_id) {
            let first = handle.close_inbox();
            let _ = crate::concurrency::stop_actor(actor_id);
            return i64::from(first);
        }
    }
    0
}

/// Receive a message from the current actor's inbox (blocking with timeout).
/// Returns NIL on timeout or when no actor inbox is available.
#[no_mangle]
pub extern "C" fn rt_actor_recv() -> RuntimeValue {
    let msg = CURRENT_ACTOR_INBOX.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|rx| rx.lock().ok())
            .and_then(|guard| guard.recv_timeout(Duration::from_secs(5)).ok())
    });

    msg.and_then(decode_inline_actor_message).unwrap_or(RuntimeValue::NIL)
}

/// Reply to parent actor by sending a message through the outbox.
/// Returns NIL. This is a void operation.
#[no_mangle]
pub extern "C" fn rt_actor_reply(message: RuntimeValue) -> RuntimeValue {
    CURRENT_ACTOR_OUTBOX.with(|cell| {
        if let Some(tx) = cell.borrow().as_ref() {
            if let Some(payload) = encode_inline_actor_message(message, TransferDomain::Actor, TransferDomain::Parent) {
                let _ = tx.try_send(payload);
            }
        }
    });
    RuntimeValue::NIL
}

/// Wait on a value (for futures/channels). Currently returns the value immediately.
/// In the future, this will block until the value is ready.
#[no_mangle]
pub extern "C" fn rt_wait(target: RuntimeValue) -> RuntimeValue {
    // For now, just return the value - proper async support will implement blocking
    target
}

/// Join an actor, waiting for it to complete.
/// Returns 1 on success, 0 on failure (invalid actor or already joined).
#[no_mangle]
pub extern "C" fn rt_actor_join(actor: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe {
            let actor_id = (*actor_ptr).actor_id;
            if let Some(handle) = get_actor_handle(actor_id) {
                match handle.join() {
                    Ok(()) => {
                        // Remove from registry after joining
                        if let Ok(mut registry) = ACTOR_REGISTRY.write() {
                            registry.remove(&actor_id);
                        }
                        return 1;
                    }
                    Err(err) => {
                        // Surface why the join failed instead of a bare 0: the
                        // body's panic message was recorded at panic time and
                        // stays queryable via rt_actor_death_reason.
                        let reason = crate::concurrency::actor_death_reason(actor_id).unwrap_or(err);
                        eprintln!("[simple-actor] join of actor {actor_id} failed: {reason}");
                        return 0;
                    }
                }
            }
        }
    }
    0
}

/// Return the recorded death reason for an actor whose body panicked,
/// or NIL when the actor is alive or exited normally.
#[no_mangle]
pub extern "C" fn rt_actor_death_reason(actor: RuntimeValue) -> RuntimeValue {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        let actor_id = unsafe { (*actor_ptr).actor_id };
        if let Some(msg) = crate::concurrency::actor_death_reason(actor_id) {
            return unsafe { crate::value::rt_string_new(msg.as_ptr(), msg.len() as u64) };
        }
    }
    RuntimeValue::NIL
}

/// Get the actor ID.
#[no_mangle]
pub extern "C" fn rt_actor_id(actor: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe { (*actor_ptr).actor_id as i64 }
    } else {
        0
    }
}

/// Check if an actor is still running.
/// Returns 1 if running, 0 if not.
#[no_mangle]
pub extern "C" fn rt_actor_is_alive(actor: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe {
            let actor_id = (*actor_ptr).actor_id;
            if let Some(handle) = get_actor_handle(actor_id) {
                if handle.is_running() && handle.is_inbox_open() {
                    return 1;
                }
            }
        }
    }
    0
}

/// Clear all actor handles (for test cleanup)
pub fn clear_actor_registry() {
    ACTOR_REGISTRY.write().unwrap().clear();
}

#[cfg(test)]
#[path = "actor_tests.rs"]
mod tests;
