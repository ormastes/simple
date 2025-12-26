//! Actor operations and FFI functions.

use std::cell::RefCell;
use std::sync::{mpsc, Arc, Mutex};
use std::time::Duration;

use super::collections::rt_string_new;
use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};
use crate::concurrency::{spawn_actor, ActorHandle, Message};

thread_local! {
    pub(crate) static CURRENT_ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = RefCell::new(None);
    pub(crate) static CURRENT_ACTOR_OUTBOX: RefCell<Option<mpsc::Sender<Message>>> = RefCell::new(None);
}

/// A heap-allocated actor handle
#[repr(C)]
pub struct RuntimeActor {
    pub header: HeapHeader,
    pub handle: ActorHandle,
}

fn alloc_actor(handle: ActorHandle) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeActor>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeActor;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Actor, size as u32);
        (*ptr).handle = handle;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_actor_ptr(value: RuntimeValue) -> Option<*mut RuntimeActor> {
    if !value.is_heap() {
        return None;
    }

    let ptr = value.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Actor {
            return None;
        }
        Some(ptr as *mut RuntimeActor)
    }
}

/// Spawn a new actor. `body_func` is a pointer to the actor body.
/// Returns a heap-allocated actor handle.
#[no_mangle]
pub extern "C" fn rt_actor_spawn(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    // Interpret body_func as an extern "C" fn(ctx: *const u8) and run it inside the actor thread.
    // If body_func is 0, spawn a no-op actor that still owns a mailbox.
    let func: Option<extern "C" fn(*const u8)> = if body_func == 0 {
        None
    } else {
        Some(unsafe { std::mem::transmute(body_func as usize) })
    };
    let ctx_ptr: usize = if ctx.is_heap() {
        ctx.as_heap_ptr() as usize
    } else {
        0
    };
    let handle = spawn_actor(move |inbox, outbox| {
        let inbox = Arc::new(Mutex::new(inbox));
        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));

        if let Some(f) = func {
            let raw_ctx = if ctx_ptr == 0 {
                std::ptr::null()
            } else {
                ctx_ptr as *const u8
            };
            f(raw_ctx);
        }

        CURRENT_ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
        CURRENT_ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
    });

    alloc_actor(handle)
}

/// Send a runtime value to an actor. Messages are transported as raw bits.
#[no_mangle]
pub extern "C" fn rt_actor_send(actor: RuntimeValue, message: RuntimeValue) {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe {
            let bits = message.to_raw();
            let payload = Message::Bytes(bits.to_le_bytes().to_vec());
            let _ = (*actor_ptr).handle.send(payload);
        }
    }
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

    match msg {
        Some(Message::Bytes(bytes)) if bytes.len() >= 8 => {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[..8]);
            RuntimeValue::from_raw(u64::from_le_bytes(buf))
        }
        Some(Message::Value(s)) => rt_string_new(s.as_ptr(), s.len() as u64),
        _ => RuntimeValue::NIL,
    }
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
            let id = (*actor_ptr).handle.id();
            match crate::concurrency::join_actor(id) {
                Ok(()) => 1,
                Err(_) => 0,
            }
        }
    } else {
        0
    }
}

/// Get the actor ID.
#[no_mangle]
pub extern "C" fn rt_actor_id(actor: RuntimeValue) -> i64 {
    if let Some(actor_ptr) = as_actor_ptr(actor) {
        unsafe { (*actor_ptr).handle.id() as i64 }
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
            // Check if the inbox sender can still send
            // This is an approximation - a proper implementation would track state
            if (*actor_ptr).handle.id() > 0 {
                1
            } else {
                0
            }
        }
    } else {
        0
    }
}
