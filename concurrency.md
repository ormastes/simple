# Simple Language Concurrency System Design

## Overview

This document specifies the complete concurrency system for the Simple programming language, including:

1. **Runtime Architecture** - Overall structure and component relationships
2. **Scheduler Design** - Work-stealing scheduler with multiple execution modes
3. **Standard Actors** - Erlang-style processes with `spawn`/`send`/`receive`
4. **Stackless Coroutine Actors** - High-performance `waitless` actors
5. **Futures and Promises** - TypeScript-style async/await integration
6. **Module Structure** - Code organization and dependencies

---

## Design Goals

| Goal | Description |
|------|-------------|
| **Performance** | Millions of concurrent actors with minimal overhead |
| **Safety** | No shared mutable state, message-passing only |
| **Flexibility** | Support both blocking and non-blocking patterns |
| **Ergonomics** | Familiar async/await syntax alongside actor model |
| **Predictability** | Deterministic execution for `waitless` code paths |

---

## Runtime Architecture

### High-Level Structure

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Simple Runtime                                │
├─────────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────┐ │
│  │   Worker    │  │   Worker    │  │   Worker    │  │  Worker    │ │
│  │  Thread 0   │  │  Thread 1   │  │  Thread 2   │  │ Thread N-1 │ │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └─────┬──────┘ │
│         │                │                │                │        │
│         └────────────────┴────────────────┴────────────────┘        │
│                                 │                                    │
│                    ┌────────────▼────────────┐                      │
│                    │   Global Scheduler      │                      │
│                    │  (Work-Stealing Deques) │                      │
│                    └────────────┬────────────┘                      │
│                                 │                                    │
│         ┌───────────────────────┼───────────────────────┐           │
│         │                       │                       │           │
│         ▼                       ▼                       ▼           │
│  ┌─────────────┐      ┌─────────────────┐      ┌──────────────┐    │
│  │  Standard   │      │    Stackless    │      │    Future    │    │
│  │   Actors    │      │     Actors      │      │   Executor   │    │
│  │  (Stackful) │      │   (Waitless)    │      │  (Async/Await)│   │
│  └─────────────┘      └─────────────────┘      └──────────────┘    │
│                                                                      │
├─────────────────────────────────────────────────────────────────────┤
│                        Shared Services                               │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐    │
│  │  Timer   │  │   I/O    │  │  Handle  │  │    Message       │    │
│  │  Wheel   │  │  Reactor │  │  Pools   │  │    Routing       │    │
│  └──────────┘  └──────────┘  └──────────┘  └──────────────────┘    │
└─────────────────────────────────────────────────────────────────────┘
```

### Core Components

| Component | Responsibility |
|-----------|---------------|
| **Worker Threads** | Execute actors and futures on OS threads |
| **Global Scheduler** | Distribute work across workers, handle stealing |
| **Standard Actors** | Stackful coroutines with full blocking support |
| **Stackless Actors** | Registered waitless actors, run-to-completion |
| **Future Executor** | Poll-based async task execution |
| **Timer Wheel** | Efficient timeout and scheduling |
| **I/O Reactor** | Async I/O event notification (epoll/kqueue/iocp) |
| **Handle Pools** | Global typed object pools |
| **Message Routing** | Actor address resolution and delivery |

---

## Scheduler Design

### Work-Stealing Algorithm

The scheduler uses a work-stealing approach with per-worker local queues:

```
┌─────────────────────────────────────────────────────────────────┐
│                    Scheduler Architecture                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Worker 0              Worker 1              Worker 2            │
│  ┌──────────┐          ┌──────────┐          ┌──────────┐       │
│  │ Local    │          │ Local    │          │ Local    │       │
│  │ Deque    │◄─steal───│ Deque    │───steal─►│ Deque    │       │
│  │ [A,B,C]  │          │ [D,E]    │          │ []       │       │
│  └────┬─────┘          └────┬─────┘          └────┬─────┘       │
│       │                     │                     │              │
│       ▼                     ▼                     ▼              │
│  ┌──────────┐          ┌──────────┐          ┌──────────┐       │
│  │ Execute  │          │ Execute  │          │ Steal    │       │
│  │ Task A   │          │ Task D   │          │ from 0/1 │       │
│  └──────────┘          └──────────┘          └──────────┘       │
│                                                                  │
│  ════════════════════════════════════════════════════════════   │
│                                                                  │
│                    Global Injection Queue                        │
│                    [NewActor1, NewActor2, ...]                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Scheduler State

```rust
/// Global scheduler state
struct Scheduler {
    /// Worker threads
    workers: Vec<Worker>,
    
    /// Global queue for new tasks (MPMC)
    global_queue: ConcurrentQueue<Task>,
    
    /// Registered stackless actors by type
    actor_registry: ActorRegistry,
    
    /// Timer wheel for timeouts
    timer_wheel: TimerWheel,
    
    /// I/O reactor handle
    io_reactor: IoReactor,
    
    /// Shutdown signal
    shutdown: AtomicBool,
    
    /// Statistics
    stats: SchedulerStats,
}

/// Per-worker state
struct Worker {
    /// Worker ID
    id: WorkerId,
    
    /// Local work-stealing deque (push/pop from one end, steal from other)
    local_queue: WorkStealingDeque<Task>,
    
    /// Random number generator for stealing
    rng: FastRng,
    
    /// Thread-local storage for current context
    tls: ThreadLocalStorage,
    
    /// Parked flag for sleeping workers
    parked: AtomicBool,
    
    /// Unpark signal
    unpark_signal: Condvar,
}
```

### Task Types

```rust
/// Unified task representation
enum Task {
    /// Standard actor with suspended stack
    StandardActor(StandardActorTask),
    
    /// Stackless actor message delivery
    StacklessMessage(StacklessMessageTask),
    
    /// Future poll task
    FuturePoll(FuturePollTask),
    
    /// Timer callback
    TimerCallback(TimerTask),
    
    /// I/O ready notification
    IoReady(IoTask),
}

/// Standard actor task
struct StandardActorTask {
    actor_id: ActorId,
    /// Suspended continuation (stack pointer, registers)
    continuation: Option<Continuation>,
    /// Actor state
    state: Box<dyn ActorState>,
    /// Mailbox reference
    mailbox: Arc<Mailbox>,
}

/// Stackless actor message task
struct StacklessMessageTask {
    actor_id: ActorId,
    /// Message to deliver
    message: Box<dyn Message>,
    /// Handler function pointer
    handler: fn(&mut dyn ActorState, Box<dyn Message>),
}

/// Future poll task
struct FuturePollTask {
    future_id: FutureId,
    /// The future to poll
    future: Pin<Box<dyn Future<Output = ()>>>,
    /// Waker for rescheduling
    waker: Waker,
}
```

### Scheduling Algorithm

```rust
impl Worker {
    /// Main worker loop
    fn run(&mut self, scheduler: &Scheduler) {
        loop {
            // Check shutdown
            if scheduler.shutdown.load(Ordering::Relaxed) {
                break;
            }
            
            // Try to get work
            if let Some(task) = self.find_work(scheduler) {
                self.execute_task(task, scheduler);
            } else {
                // No work available, park the thread
                self.park(scheduler);
            }
        }
    }
    
    /// Find work using work-stealing
    fn find_work(&mut self, scheduler: &Scheduler) -> Option<Task> {
        // 1. Check local queue first (LIFO for cache locality)
        if let Some(task) = self.local_queue.pop() {
            return Some(task);
        }
        
        // 2. Check global injection queue
        if let Some(task) = scheduler.global_queue.pop() {
            return Some(task);
        }
        
        // 3. Try to steal from other workers (FIFO from victim)
        self.try_steal(scheduler)
    }
    
    /// Attempt to steal work from another worker
    fn try_steal(&mut self, scheduler: &Scheduler) -> Option<Task> {
        let num_workers = scheduler.workers.len();
        
        // Random starting point to reduce contention
        let start = self.rng.next_usize() % num_workers;
        
        for i in 0..num_workers {
            let victim_id = (start + i) % num_workers;
            
            // Don't steal from self
            if victim_id == self.id.0 {
                continue;
            }
            
            // Try to steal half of victim's queue
            if let Some(task) = scheduler.workers[victim_id]
                .local_queue
                .steal_batch_and_pop(&self.local_queue)
            {
                return Some(task);
            }
        }
        
        None
    }
    
    /// Execute a single task
    fn execute_task(&mut self, task: Task, scheduler: &Scheduler) {
        // Set up thread-local context
        self.tls.set_current_worker(self.id);
        
        match task {
            Task::StandardActor(actor_task) => {
                self.execute_standard_actor(actor_task, scheduler);
            }
            Task::StacklessMessage(msg_task) => {
                self.execute_stackless_message(msg_task, scheduler);
            }
            Task::FuturePoll(future_task) => {
                self.execute_future_poll(future_task, scheduler);
            }
            Task::TimerCallback(timer_task) => {
                self.execute_timer(timer_task, scheduler);
            }
            Task::IoReady(io_task) => {
                self.execute_io_ready(io_task, scheduler);
            }
        }
    }
}
```

### Priority Levels

```rust
/// Task priority for scheduling
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Priority {
    /// System-critical tasks (timers, I/O)
    Critical = 0,
    
    /// High-priority (stackless actors, real-time)
    High = 1,
    
    /// Normal priority (standard actors, futures)
    Normal = 2,
    
    /// Low priority (background tasks)
    Low = 3,
}

impl Worker {
    /// Execute with priority awareness
    fn find_work_prioritized(&mut self, scheduler: &Scheduler) -> Option<Task> {
        // Check priority queues in order
        for priority in [Priority::Critical, Priority::High, Priority::Normal, Priority::Low] {
            if let Some(task) = self.local_queue.pop_priority(priority) {
                return Some(task);
            }
        }
        
        // Fall back to global and stealing
        self.find_work(scheduler)
    }
}
```

---

## Standard Actors (Stackful)

Standard actors are Erlang-style processes that can perform blocking operations including `receive`.

### Actor Structure

```rust
/// Standard actor state
struct StandardActor {
    /// Unique actor ID
    id: ActorId,
    
    /// Actor mailbox (MPSC queue)
    mailbox: Arc<Mailbox>,
    
    /// Execution state
    status: ActorStatus,
    
    /// Saved continuation when suspended
    continuation: Option<Continuation>,
    
    /// User-defined state
    user_state: Box<dyn Any + Send>,
    
    /// Links to other actors (for crash propagation)
    links: HashSet<ActorId>,
    
    /// Monitors watching this actor
    monitors: HashSet<MonitorRef>,
    
    /// Trap exit flag
    trap_exit: bool,
}

/// Actor execution status
enum ActorStatus {
    /// Ready to run
    Runnable,
    
    /// Waiting for message matching pattern
    ReceiveBlocked { patterns: Vec<Pattern> },
    
    /// Waiting for I/O
    IoBlocked { io_ref: IoRef },
    
    /// Waiting for timer
    TimerBlocked { timer_ref: TimerRef },
    
    /// Exited normally
    Exited { reason: ExitReason },
    
    /// Crashed with error
    Crashed { error: ActorError },
}

/// Actor mailbox
struct Mailbox {
    /// Message queue
    queue: ConcurrentQueue<Envelope>,
    
    /// Notification for waiting actor
    notify: AtomicWaker,
    
    /// Message count
    len: AtomicUsize,
}

/// Message envelope with metadata
struct Envelope {
    /// Sender PID
    from: ActorId,
    
    /// Message payload
    message: Box<dyn Message>,
    
    /// Timestamp
    timestamp: Instant,
}
```

### Spawn Implementation

```rust
/// Spawn a new standard actor
pub fn spawn<F, S>(init: F) -> Pid
where
    F: FnOnce() -> S + Send + 'static,
    S: ActorBehavior + Send + 'static,
{
    let scheduler = Scheduler::current();
    
    // Allocate actor ID
    let actor_id = scheduler.next_actor_id();
    
    // Create mailbox
    let mailbox = Arc::new(Mailbox::new());
    
    // Create actor
    let actor = StandardActor {
        id: actor_id,
        mailbox: mailbox.clone(),
        status: ActorStatus::Runnable,
        continuation: None,
        user_state: Box::new(()),
        links: HashSet::new(),
        monitors: HashSet::new(),
        trap_exit: false,
    };
    
    // Create initialization task
    let task = Task::StandardActor(StandardActorTask {
        actor_id,
        continuation: None,
        state: Box::new(actor),
        mailbox,
    });
    
    // The actual init closure will be run when the task executes
    // Store it in the task for deferred execution
    
    // Submit to scheduler
    scheduler.submit(task);
    
    // Return PID handle
    Pid::new(actor_id)
}

/// Spawn with explicit function
pub fn spawn_fn<F>(f: F) -> Pid
where
    F: FnOnce() + Send + 'static,
{
    spawn(move || {
        f();
        ()  // Return unit state
    })
}
```

### Send Implementation

```rust
/// Send a message to an actor (non-blocking)
pub fn send<M: Message + 'static>(pid: Pid, message: M) {
    let scheduler = Scheduler::current();
    
    // Look up actor mailbox
    if let Some(mailbox) = scheduler.lookup_mailbox(pid.actor_id) {
        // Create envelope
        let envelope = Envelope {
            from: current_actor_id(),
            message: Box::new(message),
            timestamp: Instant::now(),
        };
        
        // Enqueue message
        mailbox.queue.push(envelope);
        mailbox.len.fetch_add(1, Ordering::Relaxed);
        
        // Wake up actor if it's receive-blocked
        mailbox.notify.wake();
        
        // If actor was blocked, reschedule it
        scheduler.try_wake_actor(pid.actor_id);
    }
    // If actor doesn't exist, message is silently dropped
    // (Erlang semantics)
}

/// Operator syntax: pid <- message
impl<M: Message + 'static> Shl<M> for Pid {
    type Output = ();
    
    fn shl(self, message: M) {
        send(self, message);
    }
}
```

### Receive Implementation

```rust
/// Receive a message (blocking)
pub fn receive<T, F>(matcher: F) -> T
where
    F: FnMut(&dyn Message) -> Option<T>,
{
    receive_timeout(matcher, Duration::MAX).unwrap()
}

/// Receive with timeout
pub fn receive_timeout<T, F>(mut matcher: F, timeout: Duration) -> Option<T>
where
    F: FnMut(&dyn Message) -> Option<T>,
{
    let actor = current_actor();
    let deadline = Instant::now() + timeout;
    
    loop {
        // Scan mailbox for matching message
        let mut cursor = actor.mailbox.queue.cursor();
        
        while let Some(envelope) = cursor.next() {
            if let Some(result) = matcher(&*envelope.message) {
                // Remove matched message from queue
                cursor.remove_current();
                actor.mailbox.len.fetch_sub(1, Ordering::Relaxed);
                return Some(result);
            }
        }
        
        // No match found, check timeout
        let now = Instant::now();
        if now >= deadline {
            return None;
        }
        
        // Suspend actor until new message arrives or timeout
        let remaining = deadline - now;
        suspend_for_receive(remaining);
        
        // Woken up, loop to check mailbox again
    }
}

/// Suspend current actor for receive
fn suspend_for_receive(timeout: Duration) {
    let scheduler = Scheduler::current();
    let actor_id = current_actor_id();
    
    // Set up timer if needed
    let timer_ref = if timeout < Duration::MAX {
        Some(scheduler.timer_wheel.schedule(timeout, move || {
            scheduler.wake_actor(actor_id);
        }))
    } else {
        None
    };
    
    // Update actor status
    let actor = current_actor_mut();
    actor.status = ActorStatus::ReceiveBlocked {
        patterns: vec![],  // Simplified; real impl tracks patterns
    };
    
    // Save continuation and yield to scheduler
    // This is the "stackful" part - we save the entire call stack
    save_continuation_and_yield();
    
    // When we resume, cancel timer if it exists
    if let Some(ref timer_ref) = timer_ref {
        scheduler.timer_wheel.cancel(timer_ref);
    }
}
```

### Context Switching (Stackful Coroutines)

```rust
/// Continuation representing suspended execution
struct Continuation {
    /// Saved stack pointer
    stack_ptr: *mut u8,
    
    /// Saved instruction pointer
    instruction_ptr: *const u8,
    
    /// Saved registers
    registers: SavedRegisters,
    
    /// Stack memory (owned)
    stack: Stack,
}

/// Per-actor stack allocation
struct Stack {
    /// Stack memory
    memory: Box<[u8]>,
    
    /// Stack size
    size: usize,
    
    /// Guard page address
    guard_page: *mut u8,
}

impl Stack {
    /// Allocate a new stack
    fn new(size: usize) -> Self {
        // Allocate with guard page
        let total_size = size + PAGE_SIZE;
        let memory = alloc_aligned(total_size, PAGE_SIZE);
        
        // Set up guard page (no access)
        mprotect(memory.as_ptr(), PAGE_SIZE, PROT_NONE);
        
        Stack {
            memory,
            size,
            guard_page: memory.as_ptr() as *mut u8,
        }
    }
}

/// Save current continuation and switch to scheduler
#[naked]
unsafe extern "C" fn save_continuation_and_yield() {
    // Platform-specific assembly
    // x86_64 example:
    asm!(
        // Save callee-saved registers
        "push rbx",
        "push rbp",
        "push r12",
        "push r13",
        "push r14",
        "push r15",
        
        // Save stack pointer to continuation
        "mov rdi, rsp",
        "call save_stack_pointer",
        
        // Switch to scheduler stack
        "mov rsp, [scheduler_stack]",
        
        // Jump to scheduler
        "jmp scheduler_resume",
        
        options(noreturn)
    );
}

/// Resume a suspended continuation
#[naked]
unsafe extern "C" fn resume_continuation(cont: *mut Continuation) {
    asm!(
        // Load stack pointer from continuation
        "mov rsp, [rdi]",
        
        // Restore callee-saved registers
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        
        // Return to saved instruction pointer
        "ret",
        
        options(noreturn)
    );
}
```

---

## Stackless Coroutine Actors

Stackless actors are high-performance, `waitless` actors that run to completion without suspension.

### Actor Registry

```rust
/// Global registry of stackless actor types and instances
struct ActorRegistry {
    /// Registered actor types
    types: RwLock<HashMap<TypeId, ActorTypeInfo>>,
    
    /// Active actor instances by ID
    instances: ConcurrentHashMap<ActorId, StacklessActorInstance>,
    
    /// Actor ID to type mapping
    id_to_type: ConcurrentHashMap<ActorId, TypeId>,
}

/// Information about a registered actor type
struct ActorTypeInfo {
    /// Type name for debugging
    name: &'static str,
    
    /// Message handlers by message type
    handlers: HashMap<TypeId, HandlerFn>,
    
    /// State constructor
    state_constructor: fn() -> Box<dyn StacklessActorState>,
    
    /// State size for allocation
    state_size: usize,
}

/// Handler function pointer
type HandlerFn = fn(
    state: &mut dyn StacklessActorState,
    message: Box<dyn Message>,
    ctx: &mut ActorContext,
);

/// Instance of a stackless actor
struct StacklessActorInstance {
    /// Actor ID
    id: ActorId,
    
    /// Type ID for handler lookup
    type_id: TypeId,
    
    /// Actor state (inline or boxed)
    state: Box<dyn StacklessActorState>,
    
    /// Message queue
    mailbox: ConcurrentQueue<Box<dyn Message>>,
    
    /// Is currently being processed?
    processing: AtomicBool,
    
    /// Registration mode
    mode: RegistrationMode,
}

/// How the actor is scheduled
enum RegistrationMode {
    /// Registered with scheduler, auto-invoked on messages
    Registered,
    
    /// Manual invocation only
    Manual,
    
    /// Event-driven (triggered by external events)
    EventDriven { event_source: EventSourceId },
}
```

### Registration API

```rust
/// Register a stackless actor with the scheduler
pub fn register_actor<A: StacklessActor>() -> ActorHandle<A> {
    let scheduler = Scheduler::current();
    let registry = &scheduler.actor_registry;
    
    // Get or register actor type
    let type_id = TypeId::of::<A>();
    registry.types.write().entry(type_id).or_insert_with(|| {
        ActorTypeInfo {
            name: std::any::type_name::<A>(),
            handlers: A::handlers(),
            state_constructor: || Box::new(A::State::default()),
            state_size: std::mem::size_of::<A::State>(),
        }
    });
    
    // Allocate actor ID
    let actor_id = scheduler.next_actor_id();
    
    // Create instance
    let instance = StacklessActorInstance {
        id: actor_id,
        type_id,
        state: Box::new(A::State::default()),
        mailbox: ConcurrentQueue::new(),
        processing: AtomicBool::new(false),
        mode: RegistrationMode::Registered,
    };
    
    // Register instance
    registry.instances.insert(actor_id, instance);
    registry.id_to_type.insert(actor_id, type_id);
    
    ActorHandle::new(actor_id)
}

/// Create a manual-invocation actor (not auto-scheduled)
pub fn create_manual_actor<A: StacklessActor>() -> ManualActorHandle<A> {
    let scheduler = Scheduler::current();
    let registry = &scheduler.actor_registry;
    
    let type_id = TypeId::of::<A>();
    let actor_id = scheduler.next_actor_id();
    
    let instance = StacklessActorInstance {
        id: actor_id,
        type_id,
        state: Box::new(A::State::default()),
        mailbox: ConcurrentQueue::new(),
        processing: AtomicBool::new(false),
        mode: RegistrationMode::Manual,
    };
    
    registry.instances.insert(actor_id, instance);
    
    ManualActorHandle::new(actor_id)
}
```

### Sending to Stackless Actors

```rust
/// Send message to a stackless actor
pub fn send_stackless<M: Message + 'static>(handle: &ActorHandle<impl StacklessActor>, message: M) {
    let scheduler = Scheduler::current();
    let registry = &scheduler.actor_registry;
    
    let actor_id = handle.actor_id;
    
    // Enqueue message
    if let Some(instance) = registry.instances.get(&actor_id) {
        instance.mailbox.push(Box::new(message));
        
        // If registered and not currently processing, schedule it
        if matches!(instance.mode, RegistrationMode::Registered) {
            schedule_stackless_actor(actor_id, &scheduler);
        }
    }
}

/// Schedule a stackless actor for execution
fn schedule_stackless_actor(actor_id: ActorId, scheduler: &Scheduler) {
    let registry = &scheduler.actor_registry;
    
    if let Some(instance) = registry.instances.get(&actor_id) {
        // Try to claim processing rights
        if instance.processing
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            // We got the lock, create a task
            let type_id = instance.type_id;
            
            // Pop one message
            if let Some(message) = instance.mailbox.pop() {
                let task = Task::StacklessMessage(StacklessMessageTask {
                    actor_id,
                    message,
                    handler: lookup_handler(&registry, type_id, message.type_id()),
                });
                
                // Submit with high priority
                scheduler.submit_priority(task, Priority::High);
            } else {
                // No message, release lock
                instance.processing.store(false, Ordering::Release);
            }
        }
        // If already processing, the message will be picked up in the processing loop
    }
}
```

### Executing Stackless Actor Messages

```rust
impl Worker {
    /// Execute a stackless actor message
    fn execute_stackless_message(
        &mut self,
        task: StacklessMessageTask,
        scheduler: &Scheduler,
    ) {
        let registry = &scheduler.actor_registry;
        
        // Set up TLS for waitless context
        self.tls.set_context(Context::Waitless);
        self.tls.set_current_actor(task.actor_id);
        
        // Get instance
        if let Some(mut instance) = registry.instances.get_mut(&task.actor_id) {
            // Create actor context
            let mut ctx = ActorContext {
                actor_id: task.actor_id,
                scheduler,
            };
            
            // Execute handler (must be waitless - no blocking allowed)
            (task.handler)(&mut *instance.state, task.message, &mut ctx);
            
            // Check for more messages
            if let Some(next_message) = instance.mailbox.pop() {
                // Reschedule immediately for next message
                let next_task = Task::StacklessMessage(StacklessMessageTask {
                    actor_id: task.actor_id,
                    message: next_message,
                    handler: task.handler,  // Same handler type
                });
                
                // Push to local queue for immediate execution
                self.local_queue.push(next_task);
            } else {
                // No more messages, release processing lock
                instance.processing.store(false, Ordering::Release);
            }
        }
        
        // Clear TLS context
        self.tls.set_context(Context::Normal);
        self.tls.clear_current_actor();
    }
}

/// Context provided to actor handlers
struct ActorContext<'a> {
    actor_id: ActorId,
    scheduler: &'a Scheduler,
}

impl<'a> ActorContext<'a> {
    /// Send a message to another actor
    pub fn send<M: Message + 'static>(&self, pid: Pid, message: M) {
        send(pid, message);
    }
    
    /// Spawn a new actor
    pub fn spawn<A: StacklessActor>(&self) -> ActorHandle<A> {
        register_actor::<A>()
    }
    
    /// Get current actor's PID
    pub fn self_pid(&self) -> Pid {
        Pid::new(self.actor_id)
    }
}
```

### Manual Invocation

```rust
/// Handle for manually-invoked actors
struct ManualActorHandle<A: StacklessActor> {
    actor_id: ActorId,
    _marker: PhantomData<A>,
}

impl<A: StacklessActor> ManualActorHandle<A> {
    /// Process one message (if available)
    /// Returns true if a message was processed
    pub fn poll_one(&self) -> bool {
        let scheduler = Scheduler::current();
        let registry = &scheduler.actor_registry;
        
        if let Some(mut instance) = registry.instances.get_mut(&self.actor_id) {
            if let Some(message) = instance.mailbox.pop() {
                // Set up context
                let tls = ThreadLocalStorage::current();
                tls.set_context(Context::Waitless);
                tls.set_current_actor(self.actor_id);
                
                // Get handler and execute
                let type_id = instance.type_id;
                let handler = lookup_handler(&registry, type_id, message.type_id());
                
                let mut ctx = ActorContext {
                    actor_id: self.actor_id,
                    scheduler: &scheduler,
                };
                
                handler(&mut *instance.state, message, &mut ctx);
                
                // Clear context
                tls.set_context(Context::Normal);
                tls.clear_current_actor();
                
                return true;
            }
        }
        false
    }
    
    /// Process all pending messages
    pub fn drain(&self) -> usize {
        let mut count = 0;
        while self.poll_one() {
            count += 1;
        }
        count
    }
    
    /// Process messages until predicate returns false
    pub fn poll_while<F: FnMut() -> bool>(&self, mut should_continue: F) -> usize {
        let mut count = 0;
        while should_continue() && self.poll_one() {
            count += 1;
        }
        count
    }
    
    /// Send a message to this actor
    pub fn send<M: Message + 'static>(&self, message: M) {
        let scheduler = Scheduler::current();
        let registry = &scheduler.actor_registry;
        
        if let Some(instance) = registry.instances.get(&self.actor_id) {
            instance.mailbox.push(Box::new(message));
        }
    }
}
```

### Stackless Actor Macro (Code Generation)

```rust
/// Macro to define a stackless actor
/// 
/// Usage in Simple:
/// ```
/// actor Counter:
///     state:
///         value: Int = 0
///     on Inc(by: Int) waitless:
///         self.value = self.value + by
/// ```
/// 
/// Generates:
#[macro_export]
macro_rules! define_stackless_actor {
    (
        actor $name:ident:
            state:
                $($field:ident : $field_ty:ty = $default:expr),* $(,)?
            $(
                on $msg_name:ident($($param:ident : $param_ty:ty),*) waitless:
                    $handler_body:block
            )*
    ) => {
        // State struct
        struct $name##State {
            $($field: $field_ty),*
        }
        
        impl Default for $name##State {
            fn default() -> Self {
                Self {
                    $($field: $default),*
                }
            }
        }
        
        // Message types
        $(
            struct $msg_name {
                $($param: $param_ty),*
            }
            
            impl Message for $msg_name {
                fn type_id(&self) -> TypeId {
                    TypeId::of::<$msg_name>()
                }
            }
        )*
        
        // Actor implementation
        struct $name;
        
        impl StacklessActor for $name {
            type State = $name##State;
            
            fn handlers() -> HashMap<TypeId, HandlerFn> {
                let mut map = HashMap::new();
                $(
                    map.insert(
                        TypeId::of::<$msg_name>(),
                        |state: &mut dyn StacklessActorState, msg: Box<dyn Message>, ctx: &mut ActorContext| {
                            let state = state.downcast_mut::<$name##State>().unwrap();
                            let msg = msg.downcast::<$msg_name>().unwrap();
                            let $($param = msg.$param;)*
                            $handler_body
                        }
                    );
                )*
                map
            }
        }
    };
}
```

---

## Futures and Promises

Simple provides TypeScript-style async/await built on top of the actor system.

### Future Type

```rust
/// A future representing an asynchronous computation
/// Similar to TypeScript's Promise<T>
enum Future<T> {
    /// Not yet started
    Pending,
    
    /// Currently executing
    Running {
        /// Underlying task
        task: Pin<Box<dyn PollableFuture<Output = T>>>,
        /// Waker for notification
        waker: Option<Waker>,
    },
    
    /// Completed successfully
    Resolved(T),
    
    /// Completed with error
    Rejected(Error),
}

/// Promise - the writable end of a Future
/// Like TypeScript's resolve/reject callbacks
struct Promise<T> {
    /// Shared state with the Future
    shared: Arc<PromiseShared<T>>,
}

struct PromiseShared<T> {
    /// Current state
    state: Mutex<PromiseState<T>>,
    
    /// Notification for waiters
    notify: Condvar,
    
    /// Wakers to wake on completion
    wakers: Mutex<Vec<Waker>>,
}

enum PromiseState<T> {
    Pending,
    Resolved(T),
    Rejected(Error),
}
```

### Creating Futures

```rust
/// Create a new future/promise pair
pub fn promise<T>() -> (Future<T>, Promise<T>) {
    let shared = Arc::new(PromiseShared {
        state: Mutex::new(PromiseState::Pending),
        notify: Condvar::new(),
        wakers: Mutex::new(Vec::new()),
    });
    
    let future = Future::Running {
        task: Box::pin(PromiseFuture { shared: shared.clone() }),
        waker: None,
    };
    
    let promise = Promise { shared };
    
    (future, promise)
}

impl<T> Promise<T> {
    /// Resolve the promise with a value
    pub fn resolve(self, value: T) {
        let mut state = self.shared.state.lock();
        *state = PromiseState::Resolved(value);
        
        // Wake all waiters
        self.shared.notify.notify_all();
        for waker in self.shared.wakers.lock().drain(..) {
            waker.wake();
        }
    }
    
    /// Reject the promise with an error
    pub fn reject(self, error: Error) {
        let mut state = self.shared.state.lock();
        *state = PromiseState::Rejected(error);
        
        self.shared.notify.notify_all();
        for waker in self.shared.wakers.lock().drain(..) {
            waker.wake();
        }
    }
}
```

### Async/Await Implementation

```rust
/// Await a future (can only be called in async context)
pub async fn await_future<T>(future: Future<T>) -> Result<T, Error> {
    match future {
        Future::Resolved(value) => Ok(value),
        Future::Rejected(error) => Err(error),
        Future::Pending => {
            // This shouldn't happen - pending futures should be Running
            Err(Error::InvalidFutureState)
        }
        Future::Running { task, .. } => {
            task.await
        }
    }
}

/// The `async` function transformation
/// 
/// ```simple
/// fn fetch_data() async -> Data:
///     let response = await http_get("https://api.example.com")
///     return parse(response)
/// ```
/// 
/// Becomes:
/// ```rust
/// fn fetch_data() -> Future<Data> {
///     Future::Running {
///         task: Box::pin(async move {
///             let response = http_get("https://api.example.com").await?;
///             Ok(parse(response))
///         }),
///         waker: None,
///     }
/// }
/// ```

/// State machine for async functions
enum AsyncFnState<T> {
    /// Initial state
    Start,
    
    /// Waiting on a sub-future
    Waiting {
        sub_future: Pin<Box<dyn PollableFuture<Output = T>>>,
        resume_point: usize,
    },
    
    /// Completed
    Done,
}
```

### Future Combinators

```rust
impl<T: Send + 'static> Future<T> {
    /// Transform the result (like Promise.then)
    pub fn then<U, F>(self, f: F) -> Future<U>
    where
        F: FnOnce(T) -> U + Send + 'static,
        U: Send + 'static,
    {
        Future::Running {
            task: Box::pin(async move {
                let value = self.await?;
                Ok(f(value))
            }),
            waker: None,
        }
    }
    
    /// Handle errors (like Promise.catch)
    pub fn catch<F>(self, f: F) -> Future<T>
    where
        F: FnOnce(Error) -> T + Send + 'static,
    {
        Future::Running {
            task: Box::pin(async move {
                match self.await {
                    Ok(value) => Ok(value),
                    Err(error) => Ok(f(error)),
                }
            }),
            waker: None,
        }
    }
    
    /// Always run (like Promise.finally)
    pub fn finally<F>(self, f: F) -> Future<T>
    where
        F: FnOnce() + Send + 'static,
    {
        Future::Running {
            task: Box::pin(async move {
                let result = self.await;
                f();
                result
            }),
            waker: None,
        }
    }
    
    /// Wait for all futures (like Promise.all)
    pub fn all<I>(futures: I) -> Future<Vec<T>>
    where
        I: IntoIterator<Item = Future<T>>,
    {
        let futures: Vec<_> = futures.into_iter().collect();
        
        Future::Running {
            task: Box::pin(async move {
                let mut results = Vec::with_capacity(futures.len());
                for future in futures {
                    results.push(future.await?);
                }
                Ok(results)
            }),
            waker: None,
        }
    }
    
    /// Wait for first to complete (like Promise.race)
    pub fn race<I>(futures: I) -> Future<T>
    where
        I: IntoIterator<Item = Future<T>>,
    {
        let futures: Vec<_> = futures.into_iter().collect();
        
        Future::Running {
            task: Box::pin(async move {
                // Use select! or similar to race futures
                race_impl(futures).await
            }),
            waker: None,
        }
    }
    
    /// Wait for any success (like Promise.any)
    pub fn any<I>(futures: I) -> Future<T>
    where
        I: IntoIterator<Item = Future<T>>,
    {
        let futures: Vec<_> = futures.into_iter().collect();
        
        Future::Running {
            task: Box::pin(async move {
                let mut errors = Vec::new();
                for future in futures {
                    match future.await {
                        Ok(value) => return Ok(value),
                        Err(e) => errors.push(e),
                    }
                }
                Err(Error::AllRejected(errors))
            }),
            waker: None,
        }
    }
    
    /// Settle all futures (like Promise.allSettled)
    pub fn all_settled<I>(futures: I) -> Future<Vec<SettledResult<T>>>
    where
        I: IntoIterator<Item = Future<T>>,
    {
        let futures: Vec<_> = futures.into_iter().collect();
        
        Future::Running {
            task: Box::pin(async move {
                let mut results = Vec::with_capacity(futures.len());
                for future in futures {
                    let settled = match future.await {
                        Ok(value) => SettledResult::Fulfilled(value),
                        Err(error) => SettledResult::Rejected(error),
                    };
                    results.push(settled);
                }
                Ok(results)
            }),
            waker: None,
        }
    }
}

/// Result from allSettled
enum SettledResult<T> {
    Fulfilled(T),
    Rejected(Error),
}
```

### Future Executor Integration

```rust
impl Worker {
    /// Execute a future poll task
    fn execute_future_poll(
        &mut self,
        mut task: FuturePollTask,
        scheduler: &Scheduler,
    ) {
        // Create poll context with waker
        let waker = task.waker.clone();
        let mut cx = std::task::Context::from_waker(&waker);
        
        // Poll the future
        match task.future.as_mut().poll(&mut cx) {
            Poll::Ready(()) => {
                // Future completed, clean up
                scheduler.remove_future(task.future_id);
            }
            Poll::Pending => {
                // Future not ready, it will be rescheduled when woken
                scheduler.park_future(task);
            }
        }
    }
}

/// Waker implementation for Simple futures
struct SimpleWaker {
    future_id: FutureId,
    scheduler: Arc<Scheduler>,
}

impl Wake for SimpleWaker {
    fn wake(self: Arc<Self>) {
        // Reschedule the future
        self.scheduler.wake_future(self.future_id);
    }
}
```

---

## Timer Wheel

Efficient timeout scheduling using a hierarchical timer wheel.

### Timer Wheel Structure

```
┌─────────────────────────────────────────────────────────────────┐
│                    Hierarchical Timer Wheel                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Level 0 (1ms granularity, 256 slots = 256ms)                   │
│  ┌─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┐     │
│  │0│1│2│3│4│5│6│7│...                               ...│255│     │
│  └─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┘     │
│        ▲                                                         │
│        │ current                                                 │
│                                                                  │
│  Level 1 (256ms granularity, 64 slots = 16.4s)                  │
│  ┌─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┐     │
│  │0│1│2│3│4│5│6│7│...                                │63│        │
│  └─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┘     │
│                                                                  │
│  Level 2 (16.4s granularity, 64 slots = 17.5min)                │
│  ┌─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┐     │
│  │0│1│2│3│4│5│6│7│...                                │63│        │
│  └─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┘     │
│                                                                  │
│  Level 3 (overflow - arbitrary long timeouts)                    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ BTreeMap<Instant, Vec<Timer>>                           │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Timer Implementation

```rust
/// Hierarchical timer wheel
struct TimerWheel {
    /// Current time (in ticks)
    current_tick: AtomicU64,
    
    /// Level 0: 1ms slots
    level0: [Mutex<Vec<TimerEntry>>; 256],
    
    /// Level 1: 256ms slots  
    level1: [Mutex<Vec<TimerEntry>>; 64],
    
    /// Level 2: 16.4s slots
    level2: [Mutex<Vec<TimerEntry>>; 64],
    
    /// Overflow for very long timers
    overflow: Mutex<BTreeMap<u64, Vec<TimerEntry>>>,
    
    /// Timer ID counter
    next_id: AtomicU64,
}

struct TimerEntry {
    id: TimerId,
    deadline: u64,  // Absolute tick
    callback: Box<dyn FnOnce() + Send>,
    cancelled: AtomicBool,
}

impl TimerWheel {
    /// Schedule a timer
    pub fn schedule<F>(&self, delay: Duration, callback: F) -> TimerRef
    where
        F: FnOnce() + Send + 'static,
    {
        let id = TimerId(self.next_id.fetch_add(1, Ordering::Relaxed));
        let current = self.current_tick.load(Ordering::Relaxed);
        let delay_ticks = duration_to_ticks(delay);
        let deadline = current + delay_ticks;
        
        let entry = TimerEntry {
            id,
            deadline,
            callback: Box::new(callback),
            cancelled: AtomicBool::new(false),
        };
        
        // Insert into appropriate level
        if delay_ticks < 256 {
            // Level 0
            let slot = (deadline % 256) as usize;
            self.level0[slot].lock().push(entry);
        } else if delay_ticks < 256 * 64 {
            // Level 1
            let slot = ((deadline / 256) % 64) as usize;
            self.level1[slot].lock().push(entry);
        } else if delay_ticks < 256 * 64 * 64 {
            // Level 2
            let slot = ((deadline / (256 * 64)) % 64) as usize;
            self.level2[slot].lock().push(entry);
        } else {
            // Overflow
            self.overflow.lock().entry(deadline).or_default().push(entry);
        }
        
        TimerRef { id, wheel: self as *const _ }
    }
    
    /// Advance time and fire ready timers
    pub fn tick(&self, scheduler: &Scheduler) {
        let current = self.current_tick.fetch_add(1, Ordering::Relaxed);
        let new_tick = current + 1;
        
        // Process level 0 slot
        let slot0 = (new_tick % 256) as usize;
        let mut timers = std::mem::take(&mut *self.level0[slot0].lock());
        
        for timer in timers.drain(..) {
            if !timer.cancelled.load(Ordering::Relaxed) {
                // Fire timer as a task
                let task = Task::TimerCallback(TimerTask {
                    callback: timer.callback,
                });
                scheduler.submit_priority(task, Priority::Critical);
            }
        }
        
        // Cascade from higher levels when needed
        if new_tick % 256 == 0 {
            self.cascade_level1(new_tick, scheduler);
        }
        if new_tick % (256 * 64) == 0 {
            self.cascade_level2(new_tick, scheduler);
        }
    }
    
    /// Cascade timers from level 1 to level 0
    fn cascade_level1(&self, tick: u64, scheduler: &Scheduler) {
        let slot = ((tick / 256) % 64) as usize;
        let mut timers = std::mem::take(&mut *self.level1[slot].lock());
        
        for timer in timers.drain(..) {
            if timer.cancelled.load(Ordering::Relaxed) {
                continue;
            }
            
            // Reinsert into level 0
            let slot0 = (timer.deadline % 256) as usize;
            self.level0[slot0].lock().push(timer);
        }
    }
    
    /// Cancel a timer
    pub fn cancel(&self, timer_ref: &TimerRef) {
        // Just mark as cancelled; it will be skipped when it fires
        // This avoids expensive removal from the wheel
        // The entry will be cleaned up lazily
    }
}
```

---

## I/O Reactor

Async I/O using the OS event notification system.

### Reactor Structure

```rust
/// I/O event reactor
struct IoReactor {
    /// OS-specific poller (epoll/kqueue/iocp)
    poller: Poller,
    
    /// Registered I/O sources
    sources: Slab<IoSource>,
    
    /// Event buffer
    events: Events,
    
    /// Waker for cross-thread notification
    waker: Waker,
}

struct IoSource {
    /// File descriptor / handle
    fd: RawFd,
    
    /// Interested events
    interest: Interest,
    
    /// Waker to notify on ready
    waker: Option<std::task::Waker>,
    
    /// Associated actor (if any)
    actor_id: Option<ActorId>,
}

/// I/O interest flags
bitflags! {
    struct Interest: u8 {
        const READABLE = 0b0001;
        const WRITABLE = 0b0010;
        const ERROR    = 0b0100;
        const HANGUP   = 0b1000;
    }
}

impl IoReactor {
    /// Register an I/O source
    pub fn register(&mut self, fd: RawFd, interest: Interest) -> IoRef {
        let key = self.sources.insert(IoSource {
            fd,
            interest,
            waker: None,
            actor_id: None,
        });
        
        self.poller.register(fd, key, interest);
        
        IoRef(key)
    }
    
    /// Poll for I/O events
    pub fn poll(&mut self, timeout: Option<Duration>) -> Vec<IoEvent> {
        self.events.clear();
        self.poller.poll(&mut self.events, timeout);
        
        let mut ready = Vec::new();
        
        for event in &self.events {
            let key = event.key();
            if let Some(source) = self.sources.get(key) {
                ready.push(IoEvent {
                    io_ref: IoRef(key),
                    ready: event.ready(),
                });
                
                // Wake associated waker
                if let Some(waker) = &source.waker {
                    waker.wake_by_ref();
                }
            }
        }
        
        ready
    }
}
```

### Async I/O Primitives

```rust
/// Async TCP stream
struct AsyncTcpStream {
    inner: TcpStream,
    io_ref: IoRef,
}

impl AsyncTcpStream {
    /// Async read
    pub async fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        loop {
            match self.inner.read(buf) {
                Ok(n) => return Ok(n),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    // Wait for readable
                    self.readable().await;
                }
                Err(e) => return Err(e),
            }
        }
    }
    
    /// Wait for readable
    async fn readable(&self) {
        IoReadyFuture {
            io_ref: self.io_ref,
            interest: Interest::READABLE,
        }.await
    }
}

/// Future that completes when I/O is ready
struct IoReadyFuture {
    io_ref: IoRef,
    interest: Interest,
}

impl std::future::Future for IoReadyFuture {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let reactor = IoReactor::current();
        
        if let Some(source) = reactor.sources.get_mut(self.io_ref.0) {
            if source.ready.contains(self.interest) {
                // Already ready
                source.ready.remove(self.interest);
                Poll::Ready(())
            } else {
                // Register waker
                source.waker = Some(cx.waker().clone());
                Poll::Pending
            }
        } else {
            // Source gone, complete immediately
            Poll::Ready(())
        }
    }
}
```

---

## Module Structure

### Crate Organization

```
simple_runtime/
├── Cargo.toml
├── src/
│   ├── lib.rs                 # Public API
│   ├── runtime/
│   │   ├── mod.rs             # Runtime initialization
│   │   ├── config.rs          # Configuration options
│   │   └── shutdown.rs        # Graceful shutdown
│   │
│   ├── scheduler/
│   │   ├── mod.rs             # Scheduler trait and factory
│   │   ├── work_stealing.rs   # Work-stealing implementation
│   │   ├── task.rs            # Task types
│   │   ├── worker.rs          # Worker thread logic
│   │   ├── queue.rs           # Work-stealing deque
│   │   └── stats.rs           # Scheduler statistics
│   │
│   ├── actor/
│   │   ├── mod.rs             # Actor traits
│   │   ├── standard/
│   │   │   ├── mod.rs         # Standard actor implementation
│   │   │   ├── mailbox.rs     # MPSC mailbox
│   │   │   ├── spawn.rs       # Spawn implementation
│   │   │   ├── receive.rs     # Receive implementation
│   │   │   └── context.rs     # Actor context switching
│   │   │
│   │   └── stackless/
│   │       ├── mod.rs         # Stackless actor implementation
│   │       ├── registry.rs    # Actor type registry
│   │       ├── instance.rs    # Actor instances
│   │       ├── handler.rs     # Message handlers
│   │       └── manual.rs      # Manual invocation API
│   │
│   ├── future/
│   │   ├── mod.rs             # Future type
│   │   ├── promise.rs         # Promise implementation
│   │   ├── combinator.rs      # then, catch, all, race, etc.
│   │   ├── executor.rs        # Future executor integration
│   │   └── waker.rs           # Waker implementation
│   │
│   ├── timer/
│   │   ├── mod.rs             # Timer API
│   │   ├── wheel.rs           # Hierarchical timer wheel
│   │   └── sleep.rs           # Sleep future
│   │
│   ├── io/
│   │   ├── mod.rs             # I/O API
│   │   ├── reactor.rs         # Event reactor
│   │   ├── poll.rs            # OS poller abstraction
│   │   ├── tcp.rs             # Async TCP
│   │   ├── udp.rs             # Async UDP
│   │   └── file.rs            # Async file I/O
│   │
│   ├── sync/
│   │   ├── mod.rs             # Synchronization primitives
│   │   ├── mutex.rs           # Async mutex
│   │   ├── rwlock.rs          # Async RwLock
│   │   ├── semaphore.rs       # Async semaphore
│   │   ├── channel.rs         # MPSC/broadcast channels
│   │   └── oneshot.rs         # One-shot channel
│   │
│   ├── handle/
│   │   ├── mod.rs             # Handle pool API
│   │   ├── pool.rs            # Pool implementation
│   │   └── global.rs          # Global pool registry
│   │
│   └── util/
│       ├── mod.rs
│       ├── tls.rs             # Thread-local storage
│       ├── atomic_waker.rs    # AtomicWaker
│       └── intrusive.rs       # Intrusive linked lists
│
└── tests/
    ├── actor_tests.rs
    ├── future_tests.rs
    ├── scheduler_tests.rs
    └── integration_tests.rs
```

### Module Dependencies

```
┌─────────────────────────────────────────────────────────────────┐
│                     Module Dependency Graph                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│                          ┌──────────┐                           │
│                          │  lib.rs  │                           │
│                          │ (public) │                           │
│                          └────┬─────┘                           │
│                               │                                  │
│              ┌────────────────┼────────────────┐                │
│              │                │                │                │
│              ▼                ▼                ▼                │
│       ┌──────────┐     ┌──────────┐     ┌──────────┐           │
│       │  actor   │     │  future  │     │ runtime  │           │
│       └────┬─────┘     └────┬─────┘     └────┬─────┘           │
│            │                │                │                  │
│            │                │                │                  │
│            └───────┬────────┴───────┬────────┘                  │
│                    │                │                            │
│                    ▼                ▼                            │
│             ┌──────────┐     ┌──────────┐                       │
│             │scheduler │     │  timer   │                       │
│             └────┬─────┘     └────┬─────┘                       │
│                  │                │                              │
│                  └───────┬────────┘                              │
│                          │                                       │
│                          ▼                                       │
│                   ┌──────────┐                                  │
│                   │    io    │                                  │
│                   └────┬─────┘                                  │
│                        │                                        │
│         ┌──────────────┼──────────────┐                        │
│         │              │              │                         │
│         ▼              ▼              ▼                         │
│    ┌────────┐    ┌──────────┐   ┌──────────┐                   │
│    │  sync  │    │  handle  │   │   util   │                   │
│    └────────┘    └──────────┘   └──────────┘                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Public API

```rust
// lib.rs - Public API

pub mod prelude {
    // Core types
    pub use crate::actor::{Pid, ActorHandle, ManualActorHandle};
    pub use crate::future::{Future, Promise};
    
    // Traits
    pub use crate::actor::{Actor, StacklessActor, Message};
    
    // Functions
    pub use crate::actor::{spawn, spawn_fn, send, receive, receive_timeout};
    pub use crate::actor::stackless::{register_actor, create_manual_actor};
    pub use crate::future::{promise, async_fn};
    pub use crate::timer::{sleep, timeout};
    
    // Macros
    pub use crate::define_stackless_actor;
}

// Re-exports
pub use runtime::{Runtime, RuntimeBuilder};
pub use scheduler::{Scheduler, Worker};
pub use actor::*;
pub use future::*;
pub use timer::*;
pub use io::*;
pub use sync::*;
pub use handle::*;
```

---

## Usage Examples

### Standard Actor Example

```simple
# Ping-pong with standard actors

fn ping(pong: Pid, count: Int):
    for i in 0 .. count:
        send pong, :ping
        receive:
            case :pong:
                print "Ping received pong {i}"
    send pong, :done

fn pong():
    loop:
        receive:
            case :ping:
                send sender(), :pong
            case :done:
                break

fn main():
    let pong_pid = spawn fn(): pong()
    spawn fn(): ping(pong_pid, 5)
```

### Stackless Actor Example

```simple
# Game entity with stackless actor

handle_pool Enemy:
    capacity: 10000

actor EnemyController:
    state:
        enemies: List[+Enemy] = []
        spawn_rate: Float = 0.5
        accumulated: Float = 0.0

    on Tick(dt: Float) waitless:
        self.accumulated = self.accumulated + dt
        
        while self.accumulated >= self.spawn_rate:
            self.accumulated = self.accumulated - self.spawn_rate
            let pos = random_spawn_point()
            let h = new+ Enemy(hp: 100, pos: pos)
            self.enemies->push(h)
        
        # Update all enemies
        for handle in self.enemies:
            match Enemy.handle_get_mut(handle):
                case Some(enemy):
                    enemy.pos->move_toward(player_pos(), dt * enemy.speed)
                    if enemy.hp <= 0:
                        Enemy.handle_free(handle)
                case None:
                    pass
        
        self.enemies->retain(\h: Enemy.handle_valid(h))

    on DamageAll(amount: Int) waitless:
        for handle in self.enemies:
            match Enemy.handle_get_mut(handle):
                case Some(enemy):
                    enemy.hp = enemy.hp - amount
                case None:
                    pass

# Manual invocation example
fn game_loop():
    let controller = create_manual_actor[EnemyController]()
    
    loop:
        let dt = get_delta_time()
        
        # Send tick message
        controller.send Tick(dt: dt)
        
        # Process all pending messages
        controller.drain()
        
        render()
        
        if should_quit():
            break
```

### Future/Promise Example

```simple
# Async HTTP requests with futures

fn fetch_user(id: Int) async -> User:
    let response = await http_get("https://api.example.com/users/{id}")
    return parse_user(response)

fn fetch_posts(user_id: Int) async -> List[Post]:
    let response = await http_get("https://api.example.com/users/{user_id}/posts")
    return parse_posts(response)

fn fetch_user_with_posts(id: Int) async -> UserWithPosts:
    let user = await fetch_user(id)
    let posts = await fetch_posts(id)
    return UserWithPosts(user: user, posts: posts)

# Parallel fetching
fn fetch_multiple_users(ids: List[Int]) async -> List[User]:
    let futures = ids.map \id: fetch_user(id)
    return await Future.all(futures)

# Race example
fn fetch_with_fallback(primary_url: String, fallback_url: String) async -> Data:
    return await Future.race([
        http_get(primary_url),
        delayed(100).then(\(): http_get(fallback_url))
    ])

# Promise-based callback integration
fn read_file_callback(path: String) -> Future[Bytes]:
    let (future, promise) = promise[Bytes]()
    
    # Legacy callback-based API
    fs_read_async(path, \result:
        match result:
            case Ok(data):
                promise.resolve(data)
            case Err(e):
                promise.reject(e)
    )
    
    return future

fn main() async:
    # Sequential
    let user = await fetch_user(1)
    print "User: {user.name}"
    
    # Parallel
    let users = await fetch_multiple_users([1, 2, 3, 4, 5])
    print "Fetched {users.len()} users"
    
    # With error handling
    let result = await fetch_user(999)
        .catch(\e: User.default())
        .finally(\(): print "Done")
```

### Mixed Actor and Future Example

```simple
# Actor that uses async operations

actor DataFetcher:
    state:
        cache: Dict[String, Data] = {}
        pending: Dict[String, List[Pid]] = {}

    on Fetch(url: String, reply_to: Pid) waitless:
        # Check cache first
        if self.cache.contains(url):
            send reply_to, CacheHit(data: self.cache[url])
            return
        
        # Check if already fetching
        if self.pending.contains(url):
            self.pending[url]->push(reply_to)
            return
        
        # Start new fetch
        self.pending[url] = [reply_to]
        
        # Spawn async task to do the actual fetch
        let self_pid = self.pid
        spawn_async fn():
            let data = await http_get(url)
            send self_pid, FetchComplete(url: url, data: data)

    on FetchComplete(url: String, data: Data) waitless:
        # Cache result
        self.cache[url] = data
        
        # Notify all waiters
        if self.pending.contains(url):
            for pid in self.pending[url]:
                send pid, FetchResult(data: data)
            self.pending->remove(url)
```

---

## Performance Considerations

### Scheduler Tuning

| Parameter | Default | Description |
|-----------|---------|-------------|
| `num_workers` | CPU cores | Number of worker threads |
| `local_queue_size` | 256 | Per-worker queue capacity |
| `global_queue_size` | 65536 | Global injection queue size |
| `steal_batch_size` | 32 | Tasks to steal at once |
| `park_timeout` | 1ms | How long to sleep when idle |

### Memory Layout

- Standard actors: ~2KB stack per actor (configurable)
- Stackless actors: State size only (no stack)
- Futures: ~64 bytes + closure size
- Messages: Heap allocated, passed by ownership

### Benchmarks (Target Performance)

| Operation | Target Latency |
|-----------|---------------|
| Message send (same worker) | < 100ns |
| Message send (cross-worker) | < 500ns |
| Actor spawn | < 1μs |
| Context switch (standard) | < 200ns |
| Future poll | < 50ns |
| Timer schedule | < 100ns |

---

## Summary

The Simple concurrency system provides:

| Feature | Implementation |
|---------|---------------|
| **Standard Actors** | Stackful coroutines with `receive` blocking |
| **Stackless Actors** | Registered/manual `waitless` handlers |
| **Futures/Promises** | TypeScript-style async/await |
| **Scheduler** | Work-stealing with priority levels |
| **Timers** | Hierarchical timer wheel |
| **I/O** | Async reactor (epoll/kqueue/iocp) |

**Key Design Decisions:**

1. **Two actor models** - Stackful for flexibility, stackless for performance
2. **Unified scheduler** - All task types share the work-stealing scheduler
3. **Familiar async** - TypeScript-like `Future<T>` with `then`/`catch`/`all`/`race`
4. **Manual control** - Stackless actors can be invoked manually for game loops
5. **Zero-copy messaging** - Messages passed by ownership, not copied

This architecture supports both high-level application development and low-latency systems programming within the same language.

