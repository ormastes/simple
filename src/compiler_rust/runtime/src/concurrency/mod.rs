use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex, OnceLock};
use std::thread::{self, JoinHandle};

// Re-export actor ABI types from common for convenience
pub use simple_common::actor::{ActorHandle, ActorSpawner, Message, ThreadSpawner};

// Death reasons for actors whose body panicked, keyed by actor id.
// Written only on the panic path; queried by rt_actor_death_reason.
fn death_reasons() -> &'static Mutex<HashMap<usize, String>> {
    static REASONS: OnceLock<Mutex<HashMap<usize, String>>> = OnceLock::new();
    REASONS.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Death reason recorded for an actor whose body panicked, if any.
pub fn actor_death_reason(id: usize) -> Option<String> {
    death_reasons()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(&id)
        .cloned()
}

fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

struct Scheduler {
    mailboxes: Mutex<HashMap<usize, mpsc::Sender<Message>>>,
    // Cloned actor handles: ActorHandle shares its lifecycle via Arc, so a
    // clone here lets join_actor(id) perform a REAL join. The previous design
    // registered an always-empty JoinHandle slot, so join_actor silently
    // succeeded without joining — masking hangs and panics.
    joins: Mutex<HashMap<usize, ActorHandle>>,
}

impl Scheduler {
    fn register(&self, id: usize, inbox: mpsc::Sender<Message>, handle: ActorHandle) {
        let mut mb = self.mailboxes.lock().unwrap_or_else(|e| e.into_inner());
        mb.insert(id, inbox);
        let mut joins = self.joins.lock().unwrap_or_else(|e| e.into_inner());
        joins.insert(id, handle);
    }

    fn send_to(&self, id: usize, msg: Message) -> Result<(), String> {
        let mb = self.mailboxes.lock().unwrap_or_else(|e| e.into_inner());
        mb.get(&id)
            .ok_or_else(|| format!("unknown actor id {id}"))?
            .send(msg)
            .map_err(|e| format!("send failed: {e}"))
    }

    fn join(&self, id: usize) -> Result<(), String> {
        let handle = {
            let joins = self.joins.lock().unwrap_or_else(|e| e.into_inner());
            joins.get(&id).cloned()
        };
        match handle {
            Some(handle) => handle.join().map_err(|err| actor_death_reason(id).unwrap_or(err)),
            None => Err(format!("unknown actor id {id}")),
        }
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
    let jh = thread::spawn(move || {
        // Record a death reason before the panic propagates so joiners can ask
        // why the actor died (the JoinHandle error payload alone is opaque by
        // the time rt_actor_join maps it to 0). Failure path only.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(in_rx, out_tx)));
        if let Err(payload) = result {
            let msg = panic_message(payload.as_ref());
            eprintln!("[simple-actor] actor {id} panicked: {msg}");
            death_reasons()
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(id, msg);
            std::panic::resume_unwind(payload);
        }
    });

    let handle = ActorHandle::new(id, in_tx.clone(), out_rx, Some(jh));
    // Register inbox sender + a handle clone (shared lifecycle) with the
    // scheduler so cross-actor dispatch AND join_actor(id) both work.
    scheduler().register(id, handle.inbox_sender(), handle.clone());
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
