use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex, OnceLock};
use std::thread::{self, JoinHandle};

// Re-export actor ABI types from common for convenience
pub use simple_common::actor::{ActorHandle, ActorSpawner, Message, ThreadSpawner};

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
    let jh = thread::spawn(move || f(in_rx, out_tx));

    let handle = ActorHandle::new(id, in_tx.clone(), out_rx, Some(jh));
    // Register inbox sender with scheduler for cross-actor dispatch
    let join_slot = Arc::new(Mutex::new(None::<JoinHandle<()>>));
    scheduler().register(id, handle.inbox_sender(), join_slot);
    handle
}

/// Send a message to an actor by id (scheduler dispatch).
pub fn send_to(id: usize, msg: Message) -> Result<(), String> {
    scheduler().send_to(id, msg)
}

/// Join an actor by id (scheduler join table).
pub fn join_actor(id: usize) -> Result<(), String> {
    scheduler().join(id)
}

/// Actor spawner that registers with the global scheduler.
///
/// This spawner integrates with the runtime's scheduler for cross-actor
/// message dispatch via `send_to(id, msg)`.
#[derive(Default)]
pub struct ScheduledSpawner;

impl ScheduledSpawner {
    pub fn new() -> Self {
        Self
    }
}

impl ActorSpawner for ScheduledSpawner {
    fn spawn<F>(&self, f: F) -> ActorHandle
    where
        F: FnOnce(mpsc::Receiver<Message>, mpsc::Sender<Message>) + Send + 'static,
    {
        spawn_actor(f)
    }
}
