//! Actor ABI types for compiler/runtime boundary.
//!
//! These are the stable types that the compiler targets. Runtime provides
//! implementations behind this interface.
//!
//! The `ActorSpawner` trait allows the compiler to spawn actors without
//! depending directly on runtime implementation details.

use std::sync::mpsc;
use std::sync::{Arc, Mutex};

/// Default finite actor inbox/outbox capacity. Full sends report backpressure.
pub const DEFAULT_ACTOR_MAILBOX_CAPACITY: usize = 256;

/// Message type for actor communication.
#[derive(Debug, Clone)]
pub enum Message {
    Value(String),
    Bytes(Vec<u8>),
    /// Fixed native ownership-transfer packet; avoids one heap allocation per
    /// inline actor message while preserving exact packet length.
    TransferPacket([u8; 48]),
}

/// Explicit actor lifecycle state for formal verification.
///
/// This enum makes the actor's lifecycle state explicit:
/// - `Running`: Actor is alive and can be joined
/// - `Joined`: Actor has been joined and cannot be joined again
///
/// Lean equivalent:
/// ```lean
/// inductive ActorLifecycle
///   | running (handle : JoinHandle)
///   | joined
/// ```
#[derive(Debug)]
pub enum ActorLifecycle {
    /// Actor is running and has a join handle
    Running(std::thread::JoinHandle<()>),
    /// Actor has been joined (or was created without a handle)
    Joined,
}

impl ActorLifecycle {
    /// Check if the actor is still running
    pub fn is_running(&self) -> bool {
        matches!(self, ActorLifecycle::Running(_))
    }

    /// Check if the actor has been joined
    pub fn is_joined(&self) -> bool {
        matches!(self, ActorLifecycle::Joined)
    }

    /// Transition from Running to Joined by joining the thread.
    /// Returns Ok(()) if successfully joined, Err if already joined or thread panicked.
    pub fn join(&mut self) -> Result<(), String> {
        match std::mem::replace(self, ActorLifecycle::Joined) {
            ActorLifecycle::Running(handle) => handle.join().map_err(|_| "actor panicked".to_string()),
            ActorLifecycle::Joined => {
                // Already joined, this is idempotent
                Ok(())
            }
        }
    }
}

/// Handle to an actor for sending/receiving messages.
///
/// This is an opaque handle that the compiler can use without knowing
/// the runtime's actor implementation details.
#[derive(Debug, Clone)]
pub struct ActorHandle {
    id: usize,
    inbox: Arc<Mutex<Option<mpsc::SyncSender<Message>>>>,
    outbox: Arc<Mutex<mpsc::Receiver<Message>>>,
    /// Explicit lifecycle state (replaces Option<JoinHandle>)
    lifecycle: Arc<Mutex<ActorLifecycle>>,
}

impl PartialEq for ActorHandle {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl ActorHandle {
    /// Create a new actor handle (called by runtime's spawn implementation).
    pub fn new(
        id: usize,
        inbox: mpsc::SyncSender<Message>,
        outbox: mpsc::Receiver<Message>,
        join_handle: Option<std::thread::JoinHandle<()>>,
    ) -> Self {
        let lifecycle = match join_handle {
            Some(handle) => ActorLifecycle::Running(handle),
            None => ActorLifecycle::Joined,
        };
        Self {
            id,
            inbox: Arc::new(Mutex::new(Some(inbox))),
            outbox: Arc::new(Mutex::new(outbox)),
            lifecycle: Arc::new(Mutex::new(lifecycle)),
        }
    }

    /// Get the actor's unique identifier.
    pub fn id(&self) -> usize {
        self.id
    }

    /// Send a message to this actor.
    pub fn send(&self, msg: Message) -> Result<(), String> {
        let inbox = self.inbox.lock().map_err(|_| "actor inbox lock poisoned".to_string())?;
        inbox
            .as_ref()
            .ok_or_else(|| "send failed: actor stopped".to_string())?
            .try_send(msg)
            .map_err(|e| format!("send failed: {e}"))
    }

    /// Close this handle's shared sender exactly once.
    ///
    /// Scheduler-owned sender copies must also be removed before a blocked
    /// receiver observes disconnect; runtime `stop_actor` performs both steps.
    pub fn close_inbox(&self) -> bool {
        self.inbox
            .lock()
            .map(|mut inbox| inbox.take().is_some())
            .unwrap_or(false)
    }

    /// Whether checked admission is still open for this actor.
    pub fn is_inbox_open(&self) -> bool {
        self.inbox.lock().map(|inbox| inbox.is_some()).unwrap_or(false)
    }

    /// Receive a message from this actor (blocking).
    pub fn recv(&self) -> Result<Message, String> {
        self.outbox
            .lock()
            .map_err(|_| "recv lock poisoned".to_string())?
            .recv()
            .map_err(|e| format!("recv failed: {e}"))
    }

    /// Receive with timeout.
    pub fn recv_timeout(&self, timeout: std::time::Duration) -> Result<Message, String> {
        self.outbox
            .lock()
            .map_err(|_| "recv lock poisoned".to_string())?
            .recv_timeout(timeout)
            .map_err(|e| format!("recv timeout: {e}"))
    }

    /// Try to receive without blocking.
    pub fn try_recv(&self) -> Result<Option<Message>, String> {
        let guard = self.outbox.lock().map_err(|_| "recv lock poisoned".to_string())?;
        match guard.try_recv() {
            Ok(msg) => Ok(Some(msg)),
            Err(mpsc::TryRecvError::Empty) => Ok(None),
            Err(mpsc::TryRecvError::Disconnected) => Err("channel disconnected".to_string()),
        }
    }

    /// Wait for the actor to finish.
    /// Uses explicit ActorLifecycle state machine for verification.
    pub fn join(&self) -> Result<(), String> {
        self.lifecycle
            .lock()
            .map_err(|_| "join lock poisoned".to_string())?
            .join()
    }

    /// Check if the actor is still running.
    pub fn is_running(&self) -> bool {
        self.lifecycle.lock().map(|guard| guard.is_running()).unwrap_or(false)
    }

    /// Check if the actor has been joined.
    pub fn is_joined(&self) -> bool {
        self.lifecycle.lock().map(|guard| guard.is_joined()).unwrap_or(true)
    }

    /// Get the inbox sender for registering with scheduler.
    pub fn inbox_sender(&self) -> Option<mpsc::SyncSender<Message>> {
        self.inbox.lock().ok()?.as_ref().cloned()
    }
}

/// Trait for spawning actors.
///
/// This allows the compiler to spawn actors without depending on
/// runtime implementation details. The runtime provides an implementation.
pub trait ActorSpawner: Send + Sync {
    /// Spawn a new actor that will execute the given closure.
    ///
    /// The closure receives:
    /// - `inbox`: Channel receiver for incoming messages
    /// - `outbox`: Channel sender for outgoing messages
    fn spawn<F>(&self, f: F) -> ActorHandle
    where
        F: FnOnce(mpsc::Receiver<Message>, mpsc::SyncSender<Message>) + Send + 'static;
}

/// A simple thread-based actor spawner.
///
/// This is a basic implementation that can be used when no custom
/// scheduler is needed. Each actor runs in its own OS thread.
#[derive(Default)]
pub struct ThreadSpawner {
    next_id: std::sync::atomic::AtomicUsize,
}

impl ThreadSpawner {
    pub fn new() -> Self {
        Self {
            next_id: std::sync::atomic::AtomicUsize::new(1),
        }
    }
}

impl ActorSpawner for ThreadSpawner {
    fn spawn<F>(&self, f: F) -> ActorHandle
    where
        F: FnOnce(mpsc::Receiver<Message>, mpsc::SyncSender<Message>) + Send + 'static,
    {
        use std::sync::atomic::Ordering;
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let (in_tx, in_rx) = mpsc::sync_channel(DEFAULT_ACTOR_MAILBOX_CAPACITY);
        let (out_tx, out_rx) = mpsc::sync_channel(DEFAULT_ACTOR_MAILBOX_CAPACITY);
        let jh = std::thread::spawn(move || f(in_rx, out_tx));
        ActorHandle::new(id, in_tx, out_rx, Some(jh))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actor_handle_reports_bounded_mailbox_backpressure() {
        let (in_tx, _in_rx) = mpsc::sync_channel(DEFAULT_ACTOR_MAILBOX_CAPACITY);
        let (_out_tx, out_rx) = mpsc::sync_channel(DEFAULT_ACTOR_MAILBOX_CAPACITY);
        let handle = ActorHandle::new(1, in_tx, out_rx, None);

        for i in 0..DEFAULT_ACTOR_MAILBOX_CAPACITY {
            assert!(handle.send(Message::Value(i.to_string())).is_ok());
        }
        let error = handle.send(Message::Value("full".to_string())).unwrap_err();
        assert!(error.contains("full"));
    }
}
