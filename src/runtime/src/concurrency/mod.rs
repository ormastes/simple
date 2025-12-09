use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock, mpsc};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Basic actor handle using channels; interim until scheduler lands.
#[derive(Debug, Clone)]
pub struct ActorHandle {
    id: usize,
    inbox: mpsc::Sender<Message>,
    outbox: Arc<Mutex<mpsc::Receiver<Message>>>,
    join: Arc<Mutex<Option<JoinHandle<()>>>>,
}

impl PartialEq for ActorHandle {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[derive(Debug, Clone)]
pub enum Message {
    Value(String),
    Bytes(Vec<u8>),
}

impl ActorHandle {
    pub fn id(&self) -> usize {
        self.id
    }

    pub fn send(&self, msg: Message) -> Result<(), String> {
        self.inbox.send(msg).map_err(|e| format!("send failed: {e}"))
    }

    pub fn recv(&self) -> Result<Message, String> {
        self.outbox
            .lock()
            .map_err(|_| "recv lock poisoned".to_string())?
            .recv()
            .map_err(|e| format!("recv failed: {e}"))
    }

    /// Receive with timeout to avoid deadlocks
    pub fn recv_timeout(&self, timeout: Duration) -> Result<Message, String> {
        self.outbox
            .lock()
            .map_err(|_| "recv lock poisoned".to_string())?
            .recv_timeout(timeout)
            .map_err(|e| format!("recv timeout: {e}"))
    }

    /// Try to receive without blocking
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

    /// Wait for the actor to finish. Safe to call multiple times.
    pub fn join(&self) -> Result<(), String> {
        if let Some(handle) = self.join.lock().map_err(|_| "join lock poisoned".to_string())?.take() {
            handle.join().map_err(|_| "actor panicked".to_string())?;
        }
        Ok(())
    }
}

struct Scheduler {
    mailboxes: Mutex<HashMap<usize, mpsc::Sender<Message>>>,
    joins: Mutex<HashMap<usize, Arc<Mutex<Option<JoinHandle<()>>>>>>,
}

impl Scheduler {
    fn register(&self, id: usize, inbox: mpsc::Sender<Message>, join_slot: Arc<Mutex<Option<JoinHandle<()>>>>) {
        let mut mb = self.mailboxes.lock().unwrap();
        mb.insert(id, inbox);
        let mut joins = self.joins.lock().unwrap();
        joins.insert(id, join_slot);
    }

    fn send_to(&self, id: usize, msg: Message) -> Result<(), String> {
        let mb = self.mailboxes.lock().unwrap();
        mb.get(&id)
            .ok_or_else(|| format!("unknown actor id {id}"))?
            .send(msg)
            .map_err(|e| format!("send failed: {e}"))
    }

    fn join(&self, id: usize) -> Result<(), String> {
        if let Some(slot) = self.joins.lock().unwrap().remove(&id) {
            if let Some(handle) = slot.lock().map_err(|_| "join lock poisoned".to_string())?.take() {
                handle.join().map_err(|_| "actor panicked".to_string())?;
            }
        }
        Ok(())
    }
}

fn scheduler() -> &'static Scheduler {
    static SCHEDULER: OnceLock<Scheduler> = OnceLock::new();
    SCHEDULER.get_or_init(|| Scheduler {
        mailboxes: Mutex::new(HashMap::new()),
        joins: Mutex::new(HashMap::new()),
    })
}

/// Spawn a new actor thread with mailbox setup. Returns a handle.
pub fn spawn_actor<F>(f: F) -> ActorHandle
where
    F: FnOnce(mpsc::Receiver<Message>, mpsc::Sender<Message>) + Send + 'static,
{
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT_ID: AtomicUsize = AtomicUsize::new(1);
    let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
    let (in_tx, in_rx) = mpsc::channel();
    let (out_tx, out_rx) = mpsc::channel();
    let join_slot = Arc::new(Mutex::new(None));
    let join_slot_clone = join_slot.clone();
    let jh = thread::spawn(move || f(in_rx, out_tx));
    *join_slot_clone.lock().unwrap() = Some(jh);
    scheduler().register(id, in_tx.clone(), join_slot.clone());
    ActorHandle {
        id,
        inbox: in_tx.clone(),
        outbox: Arc::new(Mutex::new(out_rx)),
        join: join_slot,
    }
}

/// Send a message to an actor by id (scheduler dispatch).
pub fn send_to(id: usize, msg: Message) -> Result<(), String> {
    scheduler().send_to(id, msg)
}

/// Join an actor by id (scheduler join table).
pub fn join_actor(id: usize) -> Result<(), String> {
    scheduler().join(id)
}
