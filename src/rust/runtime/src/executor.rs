//! Future Executor - JavaScript-style Promise/Future execution system
//!
//! Provides two execution modes:
//! - **Threaded (default)**: Futures run in a background thread pool, similar to JavaScript's event loop
//! - **Manual (embedded)**: Futures are queued and must be explicitly polled, suitable for embedded systems
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                         FutureExecutor                          │
//! ├─────────────────────────────────────────────────────────────────┤
//! │  Mode: Threaded                   │  Mode: Manual              │
//! │  ┌─────────────────────────┐     │  ┌────────────────────────┐│
//! │  │     Thread Pool         │     │  │    Pending Queue       ││
//! │  │  ┌─────┐ ┌─────┐        │     │  │  ┌─────┐ ┌─────┐       ││
//! │  │  │ W1  │ │ W2  │ ...    │     │  │  │ F1  │ │ F2  │ ...   ││
//! │  │  └─────┘ └─────┘        │     │  │  └─────┘ └─────┘       ││
//! │  │                         │     │  │                        ││
//! │  │  Futures execute in     │     │  │  Futures wait until    ││
//! │  │  background threads     │     │  │  poll() is called      ││
//! │  └─────────────────────────┘     │  └────────────────────────┘│
//! └─────────────────────────────────────────────────────────────────┘
//! ```

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, RwLock};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Execution mode for futures
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AsyncMode {
    /// Futures execute in background thread pool (default, like JavaScript)
    #[default]
    Threaded,
    /// Futures are queued and must be polled manually (for embedded systems)
    Manual,
}

/// Task wrapper for the executor
pub struct Task {
    id: u64,
    work: Box<dyn FnOnce() + Send + 'static>,
}

impl Task {
    fn new(id: u64, work: impl FnOnce() + Send + 'static) -> Self {
        Task {
            id,
            work: Box::new(work),
        }
    }

    fn execute(self) {
        (self.work)();
    }
}

/// Promise state for tracking completion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromiseState {
    Pending,
    Fulfilled,
    Rejected,
}

/// A Promise-style future that can be resolved or rejected
pub struct Promise<T> {
    state: Arc<RwLock<PromiseState>>,
    value: Arc<Mutex<Option<Result<T, String>>>>,
    waker: Arc<(Mutex<bool>, Condvar)>,
}

impl<T: Clone> Promise<T> {
    /// Create a new pending promise
    pub fn new() -> Self {
        Promise {
            state: Arc::new(RwLock::new(PromiseState::Pending)),
            value: Arc::new(Mutex::new(None)),
            waker: Arc::new((Mutex::new(false), Condvar::new())),
        }
    }

    /// Resolve the promise with a value
    pub fn resolve(&self, value: T) {
        let mut v = self.value.lock().unwrap();
        if v.is_none() {
            *v = Some(Ok(value));
            *self.state.write().unwrap() = PromiseState::Fulfilled;
            self.wake();
        }
    }

    /// Reject the promise with an error
    pub fn reject(&self, error: String) {
        let mut v = self.value.lock().unwrap();
        if v.is_none() {
            *v = Some(Err(error));
            *self.state.write().unwrap() = PromiseState::Rejected;
            self.wake();
        }
    }

    /// Wake any waiting threads
    fn wake(&self) {
        let (lock, cvar) = &*self.waker;
        let mut ready = lock.lock().unwrap();
        *ready = true;
        cvar.notify_all();
    }

    /// Get the current state
    pub fn state(&self) -> PromiseState {
        *self.state.read().unwrap()
    }

    /// Check if the promise is settled (fulfilled or rejected)
    pub fn is_settled(&self) -> bool {
        self.state() != PromiseState::Pending
    }

    /// Wait for the promise to settle and return the result
    pub fn wait(&self) -> Result<T, String> {
        let (lock, cvar) = &*self.waker;
        let mut ready = lock.lock().unwrap();
        while !*ready {
            ready = cvar.wait(ready).unwrap();
        }
        self.value
            .lock()
            .unwrap()
            .clone()
            .unwrap_or_else(|| Err("Promise not settled".to_string()))
    }

    /// Try to get the result without blocking
    pub fn try_get(&self) -> Option<Result<T, String>> {
        if self.is_settled() {
            self.value.lock().unwrap().clone()
        } else {
            None
        }
    }
}

impl<T: Clone> Clone for Promise<T> {
    fn clone(&self) -> Self {
        Promise {
            state: self.state.clone(),
            value: self.value.clone(),
            waker: self.waker.clone(),
        }
    }
}

impl<T> Default for Promise<T>
where
    T: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

/// The global future executor
pub struct FutureExecutor {
    mode: RwLock<AsyncMode>,
    /// Thread pool workers (only used in Threaded mode)
    workers: Mutex<Vec<JoinHandle<()>>>,
    /// Task queue for thread pool
    task_queue: Arc<(Mutex<VecDeque<Task>>, Condvar)>,
    /// Pending tasks for manual mode
    pending_tasks: Mutex<VecDeque<Task>>,
    /// Next task ID
    next_task_id: AtomicU64,
    /// Number of worker threads
    worker_count: AtomicUsize,
    /// Shutdown flag (Arc for thread safety)
    shutdown: Arc<AtomicBool>,
    /// Whether the executor has been started
    started: AtomicBool,
}

impl FutureExecutor {
    /// Create a new executor with the specified mode
    pub fn new(mode: AsyncMode) -> Self {
        FutureExecutor {
            mode: RwLock::new(mode),
            workers: Mutex::new(Vec::new()),
            task_queue: Arc::new((Mutex::new(VecDeque::new()), Condvar::new())),
            pending_tasks: Mutex::new(VecDeque::new()),
            next_task_id: AtomicU64::new(1),
            worker_count: AtomicUsize::new(4), // Default 4 workers
            shutdown: Arc::new(AtomicBool::new(false)),
            started: AtomicBool::new(false),
        }
    }

    /// Create a new executor with default settings (Threaded mode)
    pub fn default_executor() -> Self {
        Self::new(AsyncMode::Threaded)
    }

    /// Set the number of worker threads (only affects Threaded mode)
    pub fn set_worker_count(&self, count: usize) {
        self.worker_count.store(count.max(1), Ordering::SeqCst);
    }

    /// Get the current execution mode
    pub fn mode(&self) -> AsyncMode {
        *self.mode.read().unwrap()
    }

    /// Set the execution mode (must be called before start)
    pub fn set_mode(&self, mode: AsyncMode) {
        if !self.started.load(Ordering::SeqCst) {
            *self.mode.write().unwrap() = mode;
        }
    }

    /// Start the executor (spawns worker threads in Threaded mode)
    pub fn start(&self) {
        if self.started.swap(true, Ordering::SeqCst) {
            return; // Already started
        }

        if self.mode() == AsyncMode::Threaded {
            self.spawn_workers();
        }
    }

    /// Spawn worker threads for the thread pool
    fn spawn_workers(&self) {
        let count = self.worker_count.load(Ordering::SeqCst);
        let mut workers = self.workers.lock().unwrap();

        for i in 0..count {
            let queue = self.task_queue.clone();
            let shutdown = self.shutdown.clone();

            let handle = thread::Builder::new()
                .name(format!("simple-future-worker-{}", i))
                .spawn(move || {
                    loop {
                        let (lock, cvar) = &*queue;
                        let mut tasks = lock.lock().unwrap();

                        // Wait for a task or shutdown
                        while tasks.is_empty() && !shutdown.load(Ordering::SeqCst) {
                            tasks = cvar.wait(tasks).unwrap();
                        }

                        if shutdown.load(Ordering::SeqCst) && tasks.is_empty() {
                            break;
                        }

                        if let Some(task) = tasks.pop_front() {
                            drop(tasks); // Release lock before executing
                            task.execute();
                        }
                    }
                })
                .expect("Failed to spawn worker thread");

            workers.push(handle);
        }
    }

    /// Submit a task to the executor
    pub fn submit<F>(&self, work: F) -> u64
    where
        F: FnOnce() + Send + 'static,
    {
        let task_id = self.next_task_id.fetch_add(1, Ordering::SeqCst);
        let task = Task::new(task_id, work);

        match self.mode() {
            AsyncMode::Threaded => {
                // Ensure executor is started
                if !self.started.load(Ordering::SeqCst) {
                    self.start();
                }

                let (lock, cvar) = &*self.task_queue;
                let mut queue = lock.lock().unwrap();
                queue.push_back(task);
                cvar.notify_one();
            }
            AsyncMode::Manual => {
                // Queue for manual polling
                let mut pending = self.pending_tasks.lock().unwrap();
                pending.push_back(task);
            }
        }

        task_id
    }

    /// Poll and execute one pending task (Manual mode only)
    /// Returns true if a task was executed
    pub fn poll_one(&self) -> bool {
        if self.mode() != AsyncMode::Manual {
            return false;
        }

        let task = {
            let mut pending = self.pending_tasks.lock().unwrap();
            pending.pop_front()
        };

        if let Some(task) = task {
            task.execute();
            true
        } else {
            false
        }
    }

    /// Poll and execute all pending tasks (Manual mode only)
    /// Returns the number of tasks executed
    pub fn poll_all(&self) -> usize {
        if self.mode() != AsyncMode::Manual {
            return 0;
        }

        let mut count = 0;
        while self.poll_one() {
            count += 1;
        }
        count
    }

    /// Get the number of pending tasks (Manual mode only)
    pub fn pending_count(&self) -> usize {
        if self.mode() != AsyncMode::Manual {
            return 0;
        }
        self.pending_tasks.lock().unwrap().len()
    }

    /// Shutdown the executor
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::SeqCst);

        // Wake up all workers
        let (_, cvar) = &*self.task_queue;
        cvar.notify_all();

        // Join all workers
        let mut workers = self.workers.lock().unwrap();
        for handle in workers.drain(..) {
            let _ = handle.join();
        }
    }
}

impl Drop for FutureExecutor {
    fn drop(&mut self) {
        self.shutdown();
    }
}

// Global executor instance
lazy_static::lazy_static! {
    static ref GLOBAL_EXECUTOR: FutureExecutor = FutureExecutor::default_executor();
}

/// Get the global executor
pub fn executor() -> &'static FutureExecutor {
    &GLOBAL_EXECUTOR
}

/// Configure the global executor mode
pub fn configure_async_mode(mode: AsyncMode) {
    GLOBAL_EXECUTOR.set_mode(mode);
}

/// Configure the number of worker threads
pub fn configure_worker_count(count: usize) {
    GLOBAL_EXECUTOR.set_worker_count(count);
}

/// Submit a task to the global executor
pub fn spawn<F>(work: F) -> u64
where
    F: FnOnce() + Send + 'static,
{
    GLOBAL_EXECUTOR.submit(work)
}

/// Poll one pending task (Manual mode only)
pub fn poll_one() -> bool {
    GLOBAL_EXECUTOR.poll_one()
}

/// Poll all pending tasks (Manual mode only)
pub fn poll_all() -> usize {
    GLOBAL_EXECUTOR.poll_all()
}

/// Get the number of pending tasks
pub fn pending_count() -> usize {
    GLOBAL_EXECUTOR.pending_count()
}

/// Check if we're in manual mode
pub fn is_manual_mode() -> bool {
    GLOBAL_EXECUTOR.mode() == AsyncMode::Manual
}

// ============================================================================
// FFI Functions for Executor
// ============================================================================

/// Set the async execution mode.
/// mode: 0 = Threaded (default), 1 = Manual
/// Returns 1 on success, 0 if already started.
#[no_mangle]
pub extern "C" fn rt_executor_set_mode(mode: i64) -> i64 {
    let async_mode = match mode {
        0 => AsyncMode::Threaded,
        1 => AsyncMode::Manual,
        _ => return 0,
    };

    if GLOBAL_EXECUTOR.started.load(Ordering::SeqCst) {
        return 0;
    }

    GLOBAL_EXECUTOR.set_mode(async_mode);
    1
}

/// Get the current async execution mode.
/// Returns: 0 = Threaded, 1 = Manual
#[no_mangle]
pub extern "C" fn rt_executor_get_mode() -> i64 {
    match GLOBAL_EXECUTOR.mode() {
        AsyncMode::Threaded => 0,
        AsyncMode::Manual => 1,
    }
}

/// Start the executor (spawns worker threads in Threaded mode).
#[no_mangle]
pub extern "C" fn rt_executor_start() {
    GLOBAL_EXECUTOR.start();
}

/// Set the number of worker threads (only affects Threaded mode before start).
#[no_mangle]
pub extern "C" fn rt_executor_set_workers(count: i64) {
    if count > 0 {
        GLOBAL_EXECUTOR.set_worker_count(count as usize);
    }
}

/// Poll and execute one pending task (Manual mode only).
/// Returns 1 if a task was executed, 0 otherwise.
#[no_mangle]
pub extern "C" fn rt_executor_poll() -> i64 {
    if GLOBAL_EXECUTOR.poll_one() {
        1
    } else {
        0
    }
}

/// Poll and execute all pending tasks (Manual mode only).
/// Returns the number of tasks executed.
#[no_mangle]
pub extern "C" fn rt_executor_poll_all() -> i64 {
    GLOBAL_EXECUTOR.poll_all() as i64
}

/// Get the number of pending tasks (Manual mode only).
#[no_mangle]
pub extern "C" fn rt_executor_pending_count() -> i64 {
    GLOBAL_EXECUTOR.pending_count() as i64
}

/// Shutdown the executor and wait for all workers to finish.
#[no_mangle]
pub extern "C" fn rt_executor_shutdown() {
    GLOBAL_EXECUTOR.shutdown();
}

/// Check if the executor is in manual mode.
/// Returns 1 if manual mode, 0 if threaded mode.
#[no_mangle]
pub extern "C" fn rt_executor_is_manual() -> i64 {
    if is_manual_mode() {
        1
    } else {
        0
    }
}

// ============================================================================
// Isolated Thread Support
// ============================================================================

use crate::value::RuntimeValue;

/// Handle for an isolated thread
#[repr(C)]
pub struct IsolatedThreadHandle {
    /// Thread join handle (boxed to be FFI-safe)
    join_handle: Option<JoinHandle<RuntimeValue>>,
    /// Thread ID
    thread_id: u64,
    /// Whether the thread has been joined
    joined: AtomicBool,
}

// Track thread IDs
static NEXT_THREAD_ID: AtomicU64 = AtomicU64::new(1);

/// Spawn an isolated thread with a closure and copied data.
///
/// The closure receives the copied data and executes in a separate OS thread.
/// Communication with the main thread is only possible through channels.
///
/// # Arguments
/// * `closure_ptr` - Function pointer for the closure to execute
/// * `data` - Data to copy into the thread (must be copyable/cloneable)
///
/// # Returns
/// A thread handle that can be used to join the thread
#[no_mangle]
pub extern "C" fn rt_thread_spawn_isolated(closure_ptr: u64, data: RuntimeValue) -> u64 {
    let thread_id = NEXT_THREAD_ID.fetch_add(1, Ordering::SeqCst);

    // Convert closure pointer to a function
    let func: extern "C" fn(RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(closure_ptr) };

    // Clone data for the thread (deep copy for isolation)
    let copied_data = data.deep_copy();

    // Spawn the OS thread
    let handle = thread::Builder::new()
        .name(format!("simple-isolated-{}", thread_id))
        .spawn(move || {
            // Execute the closure with copied data
            func(copied_data)
        })
        .expect("Failed to spawn isolated thread");

    // Create and box the handle
    let thread_handle = Box::new(IsolatedThreadHandle {
        join_handle: Some(handle),
        thread_id,
        joined: AtomicBool::new(false),
    });

    Box::into_raw(thread_handle) as u64
}

/// Spawn an isolated thread with closure and two data arguments (e.g., data + channel).
#[no_mangle]
pub extern "C" fn rt_thread_spawn_isolated2(closure_ptr: u64, data1: RuntimeValue, data2: RuntimeValue) -> u64 {
    let thread_id = NEXT_THREAD_ID.fetch_add(1, Ordering::SeqCst);

    // Convert closure pointer to a function
    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue = unsafe { std::mem::transmute(closure_ptr) };

    // Clone data for the thread
    let copied_data1 = data1.deep_copy();
    let copied_data2 = data2; // Channels are already thread-safe, don't deep copy

    // Spawn the OS thread
    let handle = thread::Builder::new()
        .name(format!("simple-isolated-{}", thread_id))
        .spawn(move || func(copied_data1, copied_data2))
        .expect("Failed to spawn isolated thread");

    // Create and box the handle
    let thread_handle = Box::new(IsolatedThreadHandle {
        join_handle: Some(handle),
        thread_id,
        joined: AtomicBool::new(false),
    });

    Box::into_raw(thread_handle) as u64
}

/// Join an isolated thread and get its result.
/// This blocks until the thread completes.
///
/// # Arguments
/// * `handle` - The thread handle returned by spawn_isolated
///
/// # Returns
/// The result value from the thread, or NIL if already joined or invalid
#[no_mangle]
pub extern "C" fn rt_thread_join(handle: u64) -> RuntimeValue {
    if handle == 0 {
        return RuntimeValue::NIL;
    }

    let handle_ptr = handle as *mut IsolatedThreadHandle;

    unsafe {
        // Check if already joined
        if (*handle_ptr).joined.swap(true, Ordering::SeqCst) {
            return RuntimeValue::NIL;
        }

        // Take the join handle
        if let Some(join_handle) = (*handle_ptr).join_handle.take() {
            match join_handle.join() {
                Ok(result) => result,
                Err(_) => RuntimeValue::NIL, // Thread panicked
            }
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Check if an isolated thread has completed without blocking.
///
/// # Returns
/// 1 if completed, 0 if still running
#[no_mangle]
pub extern "C" fn rt_thread_is_done(handle: u64) -> i64 {
    if handle == 0 {
        return 1;
    }

    let handle_ptr = handle as *mut IsolatedThreadHandle;

    unsafe {
        if (*handle_ptr).joined.load(Ordering::SeqCst) {
            return 1;
        }

        // Check if the thread is finished (thread handle is_finished)
        if let Some(ref join_handle) = (*handle_ptr).join_handle {
            if join_handle.is_finished() {
                1
            } else {
                0
            }
        } else {
            1 // No handle means already joined
        }
    }
}

/// Get the thread ID of an isolated thread.
#[no_mangle]
pub extern "C" fn rt_thread_id(handle: u64) -> i64 {
    if handle == 0 {
        return 0;
    }

    let handle_ptr = handle as *mut IsolatedThreadHandle;

    unsafe { (*handle_ptr).thread_id as i64 }
}

/// Free an isolated thread handle.
/// If the thread hasn't been joined, it will be detached.
#[no_mangle]
pub extern "C" fn rt_thread_free(handle: u64) {
    if handle == 0 {
        return;
    }

    let handle_ptr = handle as *mut IsolatedThreadHandle;

    unsafe {
        // Drop the boxed handle, which will detach the thread if not joined
        drop(Box::from_raw(handle_ptr));
    }
}

/// Get the number of available CPU cores.
/// Useful for determining parallelism level.
#[no_mangle]
pub extern "C" fn rt_thread_available_parallelism() -> i64 {
    std::thread::available_parallelism()
        .map(|n| n.get() as i64)
        .unwrap_or(1)
}

/// Sleep the current thread for the specified milliseconds.
#[no_mangle]
pub extern "C" fn rt_thread_sleep(millis: i64) {
    if millis > 0 {
        thread::sleep(Duration::from_millis(millis as u64));
    }
}

/// Yield the current thread, allowing other threads to run.
#[no_mangle]
pub extern "C" fn rt_thread_yield() {
    thread::yield_now();
}

// ============================================================================
// Resource-Limited Thread Support
// ============================================================================

use crate::sandbox::limits::apply_resource_limits;
use crate::sandbox::ResourceLimits as RustResourceLimits;

/// Violation type codes for limited threads
/// These match the LimitViolation enum in Simple
const VIOLATION_NONE: i64 = 0;
const VIOLATION_CPU_TIME: i64 = 1;
const VIOLATION_MEMORY: i64 = 2;
const VIOLATION_FILE_DESCRIPTOR: i64 = 3;
const VIOLATION_THREAD_LIMIT: i64 = 4;
const VIOLATION_UNKNOWN: i64 = 5;

/// Handle for a resource-limited thread
#[repr(C)]
pub struct LimitedThreadHandle {
    /// Thread join handle
    join_handle: Option<JoinHandle<RuntimeValue>>,
    /// Thread ID
    thread_id: u64,
    /// Whether the thread has been joined
    joined: AtomicBool,
    /// Whether the thread was killed due to resource limit
    was_killed: AtomicBool,
    /// The violation type (if killed)
    violation_type: AtomicU64,
    /// The violation value (e.g., seconds exceeded, bytes exceeded)
    violation_value: AtomicU64,
    /// Resource limits applied to this thread
    cpu_time_limit: Option<u64>,
    memory_limit: Option<u64>,
    fd_limit: Option<u64>,
    thread_limit: Option<u64>,
}

/// Spawn a resource-limited isolated thread.
///
/// The thread will have resource limits applied via rlimit.
/// If any limit is -1, that resource is unlimited.
///
/// # Arguments
/// * `closure_ptr` - Function pointer for the closure to execute
/// * `data` - Data to copy into the thread
/// * `cpu_seconds` - CPU time limit in seconds (-1 for unlimited)
/// * `memory_bytes` - Memory limit in bytes (-1 for unlimited)
/// * `fd_limit` - File descriptor limit (-1 for unlimited)
/// * `thread_limit` - Thread count limit (-1 for unlimited, platform-specific)
///
/// # Returns
/// A thread handle that can be used to join the thread and check for violations
#[no_mangle]
pub extern "C" fn rt_thread_spawn_limited(
    closure_ptr: u64,
    data: RuntimeValue,
    cpu_seconds: i64,
    memory_bytes: i64,
    fd_limit: i64,
    thread_limit: i64,
) -> u64 {
    let thread_id = NEXT_THREAD_ID.fetch_add(1, Ordering::SeqCst);

    // Convert closure pointer to a function
    let func: extern "C" fn(RuntimeValue) -> RuntimeValue =
        unsafe { std::mem::transmute(closure_ptr) };

    // Clone data for the thread (deep copy for isolation)
    let copied_data = data.deep_copy();

    // Prepare resource limits
    let cpu_limit = if cpu_seconds >= 0 {
        Some(cpu_seconds as u64)
    } else {
        None
    };
    let mem_limit = if memory_bytes >= 0 {
        Some(memory_bytes as u64)
    } else {
        None
    };
    let fd_lim = if fd_limit >= 0 {
        Some(fd_limit as u64)
    } else {
        None
    };
    let thread_lim = if thread_limit >= 0 {
        Some(thread_limit as u64)
    } else {
        None
    };

    // Spawn the OS thread with resource limits
    let handle = thread::Builder::new()
        .name(format!("simple-limited-{}", thread_id))
        .spawn(move || {
            // Apply resource limits at the start of the thread
            let limits = RustResourceLimits {
                cpu_time: cpu_limit.map(Duration::from_secs),
                memory: mem_limit,
                file_descriptors: fd_lim,
                threads: thread_lim,
            };

            if let Err(e) = apply_resource_limits(&limits) {
                tracing::error!("Failed to apply resource limits: {}", e);
                // Continue execution even if limits fail to apply
            }

            // Execute the closure with copied data
            func(copied_data)
        })
        .expect("Failed to spawn limited thread");

    // Create and box the handle
    let thread_handle = Box::new(LimitedThreadHandle {
        join_handle: Some(handle),
        thread_id,
        joined: AtomicBool::new(false),
        was_killed: AtomicBool::new(false),
        violation_type: AtomicU64::new(VIOLATION_NONE as u64),
        violation_value: AtomicU64::new(0),
        cpu_time_limit: cpu_limit,
        memory_limit: mem_limit,
        fd_limit: fd_lim,
        thread_limit: thread_lim,
    });

    Box::into_raw(thread_handle) as u64
}

/// Spawn a resource-limited isolated thread with two data arguments.
#[no_mangle]
pub extern "C" fn rt_thread_spawn_limited2(
    closure_ptr: u64,
    data1: RuntimeValue,
    data2: RuntimeValue,
    cpu_seconds: i64,
    memory_bytes: i64,
    fd_limit: i64,
    thread_limit: i64,
) -> u64 {
    let thread_id = NEXT_THREAD_ID.fetch_add(1, Ordering::SeqCst);

    // Convert closure pointer to a function
    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue =
        unsafe { std::mem::transmute(closure_ptr) };

    // Clone data for the thread
    let copied_data1 = data1.deep_copy();
    let copied_data2 = data2; // Channels are already thread-safe

    // Prepare resource limits
    let cpu_limit = if cpu_seconds >= 0 {
        Some(cpu_seconds as u64)
    } else {
        None
    };
    let mem_limit = if memory_bytes >= 0 {
        Some(memory_bytes as u64)
    } else {
        None
    };
    let fd_lim = if fd_limit >= 0 {
        Some(fd_limit as u64)
    } else {
        None
    };
    let thread_lim = if thread_limit >= 0 {
        Some(thread_limit as u64)
    } else {
        None
    };

    // Spawn the OS thread with resource limits
    let handle = thread::Builder::new()
        .name(format!("simple-limited-{}", thread_id))
        .spawn(move || {
            // Apply resource limits at the start of the thread
            let limits = RustResourceLimits {
                cpu_time: cpu_limit.map(Duration::from_secs),
                memory: mem_limit,
                file_descriptors: fd_lim,
                threads: thread_lim,
            };

            if let Err(e) = apply_resource_limits(&limits) {
                tracing::error!("Failed to apply resource limits: {}", e);
            }

            // Execute the closure
            func(copied_data1, copied_data2)
        })
        .expect("Failed to spawn limited thread");

    // Create and box the handle
    let thread_handle = Box::new(LimitedThreadHandle {
        join_handle: Some(handle),
        thread_id,
        joined: AtomicBool::new(false),
        was_killed: AtomicBool::new(false),
        violation_type: AtomicU64::new(VIOLATION_NONE as u64),
        violation_value: AtomicU64::new(0),
        cpu_time_limit: cpu_limit,
        memory_limit: mem_limit,
        fd_limit: fd_lim,
        thread_limit: thread_lim,
    });

    Box::into_raw(thread_handle) as u64
}

/// Join a resource-limited thread and get its result.
/// This blocks until the thread completes.
///
/// # Returns
/// The result value from the thread, or NIL if the thread was killed/failed
#[no_mangle]
pub extern "C" fn rt_thread_join_limited(handle: u64) -> RuntimeValue {
    if handle == 0 {
        return RuntimeValue::NIL;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe {
        // Check if already joined
        if (*handle_ptr).joined.swap(true, Ordering::SeqCst) {
            return RuntimeValue::NIL;
        }

        // Take the join handle
        if let Some(join_handle) = (*handle_ptr).join_handle.take() {
            match join_handle.join() {
                Ok(result) => result,
                Err(panic_info) => {
                    // Thread panicked - check if it was due to a resource limit
                    (*handle_ptr).was_killed.store(true, Ordering::SeqCst);

                    // Try to determine the violation type from the panic message
                    if let Some(msg) = panic_info.downcast_ref::<&str>() {
                        if msg.contains("SIGXCPU") || msg.contains("CPU time") {
                            (*handle_ptr)
                                .violation_type
                                .store(VIOLATION_CPU_TIME as u64, Ordering::SeqCst);
                            if let Some(cpu_limit) = (*handle_ptr).cpu_time_limit {
                                (*handle_ptr)
                                    .violation_value
                                    .store(cpu_limit, Ordering::SeqCst);
                            }
                        } else if msg.contains("memory") || msg.contains("allocation") {
                            (*handle_ptr)
                                .violation_type
                                .store(VIOLATION_MEMORY as u64, Ordering::SeqCst);
                            if let Some(mem_limit) = (*handle_ptr).memory_limit {
                                (*handle_ptr)
                                    .violation_value
                                    .store(mem_limit, Ordering::SeqCst);
                            }
                        } else {
                            (*handle_ptr)
                                .violation_type
                                .store(VIOLATION_UNKNOWN as u64, Ordering::SeqCst);
                        }
                    } else {
                        (*handle_ptr)
                            .violation_type
                            .store(VIOLATION_UNKNOWN as u64, Ordering::SeqCst);
                    }

                    RuntimeValue::NIL
                }
            }
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Check if a limited thread was killed due to a resource violation.
///
/// # Returns
/// 1 if the thread was killed, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_thread_was_killed(handle: u64) -> i64 {
    if handle == 0 {
        return 0;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe {
        if (*handle_ptr).was_killed.load(Ordering::SeqCst) {
            1
        } else {
            0
        }
    }
}

/// Get the violation type for a killed thread.
///
/// # Returns
/// 0 = None, 1 = CPU time, 2 = Memory, 3 = FD, 4 = Thread, 5 = Unknown
#[no_mangle]
pub extern "C" fn rt_thread_get_violation_type(handle: u64) -> i64 {
    if handle == 0 {
        return VIOLATION_NONE;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe { (*handle_ptr).violation_type.load(Ordering::SeqCst) as i64 }
}

/// Get the violation value for a killed thread (e.g., the limit that was exceeded).
///
/// # Returns
/// The value associated with the violation (seconds, bytes, count, etc.)
#[no_mangle]
pub extern "C" fn rt_thread_get_violation_value(handle: u64) -> i64 {
    if handle == 0 {
        return 0;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe { (*handle_ptr).violation_value.load(Ordering::SeqCst) as i64 }
}

/// Check if a limited thread has completed without blocking.
///
/// # Returns
/// 1 if completed, 0 if still running
#[no_mangle]
pub extern "C" fn rt_thread_is_done_limited(handle: u64) -> i64 {
    if handle == 0 {
        return 1;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe {
        if (*handle_ptr).joined.load(Ordering::SeqCst) {
            return 1;
        }

        if let Some(ref join_handle) = (*handle_ptr).join_handle {
            if join_handle.is_finished() {
                1
            } else {
                0
            }
        } else {
            1
        }
    }
}

/// Get the thread ID of a limited thread.
#[no_mangle]
pub extern "C" fn rt_thread_id_limited(handle: u64) -> i64 {
    if handle == 0 {
        return 0;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe { (*handle_ptr).thread_id as i64 }
}

/// Free a limited thread handle.
#[no_mangle]
pub extern "C" fn rt_thread_free_limited(handle: u64) {
    if handle == 0 {
        return;
    }

    let handle_ptr = handle as *mut LimitedThreadHandle;

    unsafe {
        drop(Box::from_raw(handle_ptr));
    }
}

#[cfg(test)]
#[path = "executor_tests.rs"]
mod tests;
