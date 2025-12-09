//! Actor ABI types for compiler/runtime boundary.
//!
//! These are the stable types that the compiler targets. Runtime provides
//! implementations behind this interface.
//!
//! The `ActorSpawner` trait allows the compiler to spawn actors without
//! depending directly on runtime implementation details.

use std::sync::{Arc, Mutex};
use std::sync::mpsc;

/// Message type for actor communication.
#[derive(Debug, Clone)]
pub enum Message {
    Value(String),
    Bytes(Vec<u8>),
}

/// Handle to an actor for sending/receiving messages.
///
/// This is an opaque handle that the compiler can use without knowing
/// the runtime's actor implementation details.
#[derive(Debug, Clone)]
pub struct ActorHandle {
    id: usize,
    inbox: mpsc::Sender<Message>,
    outbox: Arc<Mutex<mpsc::Receiver<Message>>>,
    join_handle: Arc<Mutex<Option<std::thread::JoinHandle<()>>>>,
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
        inbox: mpsc::Sender<Message>,
        outbox: mpsc::Receiver<Message>,
        join_handle: Option<std::thread::JoinHandle<()>>,
    ) -> Self {
        Self {
            id,
            inbox,
            outbox: Arc::new(Mutex::new(outbox)),
            join_handle: Arc::new(Mutex::new(join_handle)),
        }
    }

    /// Get the actor's unique identifier.
    pub fn id(&self) -> usize {
        self.id
    }

    /// Send a message to this actor.
    pub fn send(&self, msg: Message) -> Result<(), String> {
        self.inbox.send(msg).map_err(|e| format!("send failed: {e}"))
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
        let guard = self.outbox
            .lock()
            .map_err(|_| "recv lock poisoned".to_string())?;
        match guard.try_recv() {
            Ok(msg) => Ok(Some(msg)),
            Err(mpsc::TryRecvError::Empty) => Ok(None),
            Err(mpsc::TryRecvError::Disconnected) => Err("channel disconnected".to_string()),
        }
    }

    /// Wait for the actor to finish.
    pub fn join(&self) -> Result<(), String> {
        if let Some(handle) = self.join_handle.lock().map_err(|_| "join lock poisoned".to_string())?.take() {
            handle.join().map_err(|_| "actor panicked".to_string())?;
        }
        Ok(())
    }

    /// Get the inbox sender for registering with scheduler.
    pub fn inbox_sender(&self) -> mpsc::Sender<Message> {
        self.inbox.clone()
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
        F: FnOnce(mpsc::Receiver<Message>, mpsc::Sender<Message>) + Send + 'static;
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
        F: FnOnce(mpsc::Receiver<Message>, mpsc::Sender<Message>) + Send + 'static,
    {
        use std::sync::atomic::Ordering;
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let (in_tx, in_rx) = mpsc::channel();
        let (out_tx, out_rx) = mpsc::channel();
        let jh = std::thread::spawn(move || f(in_rx, out_tx));
        ActorHandle::new(id, in_tx, out_rx, Some(jh))
    }
}
