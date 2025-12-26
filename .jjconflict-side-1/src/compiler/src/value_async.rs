// Async and concurrent value types for the interpreter
// These are split from value.rs for maintainability
// Note: This file is included via include!() - imports come from parent value.rs
//
// Supports two execution modes:
// - Threaded (default): Futures execute in background thread pool (like JavaScript)
// - Manual (embedded): Futures are queued and must be polled manually

use simple_runtime::{executor, is_manual_mode};
use std::sync::Condvar;

/// Execution state for a future
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FutureState {
    /// Future has not started execution
    Pending,
    /// Future is currently executing
    Running,
    /// Future completed successfully
    Fulfilled,
    /// Future completed with an error
    Rejected,
}

/// A future that wraps a computation with configurable execution mode
pub struct FutureValue {
    /// The result once computed
    result: Arc<Mutex<Option<Result<Value, String>>>>,
    /// Thread join handle (for threaded mode)
    handle: Arc<Mutex<Option<std::thread::JoinHandle<()>>>>,
    /// Current state
    state: Arc<Mutex<FutureState>>,
    /// Waker for blocking await
    waker: Arc<(Mutex<bool>, Condvar)>,
    /// The work to execute (for manual mode)
    work: Arc<Mutex<Option<Box<dyn FnOnce() -> Result<Value, String> + Send + 'static>>>>,
}

impl std::fmt::Debug for FutureValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FutureValue")
            .field("state", &self.state())
            .field("is_ready", &self.is_ready())
            .finish()
    }
}

impl FutureValue {
    /// Create a new future from a computation
    /// In Threaded mode: Immediately starts execution in background thread
    /// In Manual mode: Queues the work for later polling
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce() -> Result<Value, String> + Send + 'static,
    {
        let result: Arc<Mutex<Option<Result<Value, String>>>> = Arc::new(Mutex::new(None));
        let state = Arc::new(Mutex::new(FutureState::Pending));
        let waker = Arc::new((Mutex::new(false), Condvar::new()));

        if is_manual_mode() {
            // Manual mode: store work for later polling
            FutureValue {
                result,
                handle: Arc::new(Mutex::new(None)),
                state,
                waker,
                work: Arc::new(Mutex::new(Some(Box::new(f)))),
            }
        } else {
            // Threaded mode: spawn in executor's thread pool
            let result_clone = result.clone();
            let state_clone = state.clone();
            let waker_clone = waker.clone();

            *state.lock().unwrap() = FutureState::Running;

            // Submit to the executor's thread pool
            executor().submit(move || {
                let res = f();
                let mut result_guard = result_clone.lock().unwrap();
                *result_guard = Some(res.clone());

                // Update state
                let mut state_guard = state_clone.lock().unwrap();
                *state_guard = if res.is_ok() {
                    FutureState::Fulfilled
                } else {
                    FutureState::Rejected
                };
                drop(state_guard);

                // Wake any waiting threads
                let (lock, cvar) = &*waker_clone;
                let mut ready = lock.lock().unwrap();
                *ready = true;
                cvar.notify_all();
            });

            FutureValue {
                result,
                handle: Arc::new(Mutex::new(None)),
                state,
                waker,
                work: Arc::new(Mutex::new(None)),
            }
        }
    }

    /// Create a future that is already resolved with a value
    pub fn resolved(value: Value) -> Self {
        let result = Arc::new(Mutex::new(Some(Ok(value))));
        let state = Arc::new(Mutex::new(FutureState::Fulfilled));
        let waker = Arc::new((Mutex::new(true), Condvar::new()));
        FutureValue {
            result,
            handle: Arc::new(Mutex::new(None)),
            state,
            waker,
            work: Arc::new(Mutex::new(None)),
        }
    }

    /// Create a future that is already rejected with an error
    pub fn rejected(error: String) -> Self {
        let result = Arc::new(Mutex::new(Some(Err(error))));
        let state = Arc::new(Mutex::new(FutureState::Rejected));
        let waker = Arc::new((Mutex::new(true), Condvar::new()));
        FutureValue {
            result,
            handle: Arc::new(Mutex::new(None)),
            state,
            waker,
            work: Arc::new(Mutex::new(None)),
        }
    }

    /// Poll the future (Manual mode only)
    /// Returns true if the future completed, false if still pending
    pub fn poll(&self) -> bool {
        // Check if already completed
        if self.is_ready() {
            return true;
        }

        // Take and execute the work if present
        let work = self.work.lock().unwrap().take();
        if let Some(f) = work {
            *self.state.lock().unwrap() = FutureState::Running;

            let res = f();
            let mut result_guard = self.result.lock().unwrap();
            *result_guard = Some(res.clone());

            let mut state_guard = self.state.lock().unwrap();
            *state_guard = if res.is_ok() {
                FutureState::Fulfilled
            } else {
                FutureState::Rejected
            };

            // Wake any waiting threads
            let (lock, cvar) = &*self.waker;
            let mut ready = lock.lock().unwrap();
            *ready = true;
            cvar.notify_all();

            true
        } else {
            false
        }
    }

    /// Wait for the future to complete and return the result
    pub fn await_result(&self) -> Result<Value, String> {
        // In manual mode, poll first
        if is_manual_mode() {
            self.poll();
        }

        // First, join the thread if it's still running (legacy path)
        if let Some(handle) = self.handle.lock().unwrap().take() {
            let _ = handle.join();
        }

        // Wait for completion using condvar
        let (lock, cvar) = &*self.waker;
        let mut ready = lock.lock().unwrap();
        while !*ready && !self.is_ready() {
            ready = cvar.wait(ready).unwrap();
        }

        // Then get the result
        self.result
            .lock()
            .unwrap()
            .clone()
            .unwrap_or(Err("future result not available".to_string()))
    }

    /// Check if the future is completed without blocking
    pub fn is_ready(&self) -> bool {
        let state = *self.state.lock().unwrap();
        state == FutureState::Fulfilled || state == FutureState::Rejected
    }

    /// Get the current state
    pub fn state(&self) -> FutureState {
        *self.state.lock().unwrap()
    }
}

impl Clone for FutureValue {
    fn clone(&self) -> Self {
        FutureValue {
            result: self.result.clone(),
            handle: self.handle.clone(),
            state: self.state.clone(),
            waker: self.waker.clone(),
            work: self.work.clone(),
        }
    }
}

impl PartialEq for FutureValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.result, &other.result)
    }
}

/// Generator state for stackless coroutines
#[derive(Debug, Clone, PartialEq)]
pub enum GeneratorState {
    /// Initial state, not yet started
    Created,
    /// Suspended at a yield point, waiting to be resumed
    Suspended,
    /// Completed (returned or exhausted)
    Completed,
}

/// A stackless coroutine/generator that can yield values
/// Uses a simple iterator-based model where we collect all yields upfront
#[derive(Debug)]
pub struct GeneratorValue {
    /// Pre-computed yielded values (simple implementation)
    values: Arc<Mutex<Vec<Value>>>,
    /// Current index into values
    index: Arc<Mutex<usize>>,
    /// Current state
    state: Arc<Mutex<GeneratorState>>,
}

impl GeneratorValue {
    /// Create a new generator with pre-computed values
    pub fn new_with_values(values: Vec<Value>) -> Self {
        GeneratorValue {
            values: Arc::new(Mutex::new(values)),
            index: Arc::new(Mutex::new(0)),
            state: Arc::new(Mutex::new(GeneratorState::Created)),
        }
    }

    /// Get the next yielded value
    pub fn next(&self) -> Option<Value> {
        let mut state = self.state.lock().unwrap();
        if *state == GeneratorState::Completed {
            return None;
        }
        *state = GeneratorState::Suspended;
        drop(state);

        let values = self.values.lock().unwrap();
        let mut index = self.index.lock().unwrap();

        if *index < values.len() {
            let val = values[*index].clone();
            *index += 1;

            // Check if exhausted
            if *index >= values.len() {
                drop(index);
                drop(values);
                *self.state.lock().unwrap() = GeneratorState::Completed;
            }

            Some(val)
        } else {
            drop(index);
            drop(values);
            *self.state.lock().unwrap() = GeneratorState::Completed;
            None
        }
    }

    /// Check if the generator is exhausted
    pub fn is_done(&self) -> bool {
        *self.state.lock().unwrap() == GeneratorState::Completed
    }

    /// Collect all remaining values into an array
    pub fn collect_remaining(&self) -> Vec<Value> {
        let mut results = Vec::new();
        while let Some(val) = self.next() {
            results.push(val);
        }
        results
    }
}

impl Clone for GeneratorValue {
    fn clone(&self) -> Self {
        // Share the same underlying state so iteration continues
        GeneratorValue {
            values: self.values.clone(),
            index: self.index.clone(),
            state: self.state.clone(),
        }
    }
}

impl PartialEq for GeneratorValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.values, &other.values)
    }
}

/// A channel for inter-thread communication
#[derive(Debug)]
pub struct ChannelValue {
    sender: std::sync::mpsc::Sender<Value>,
    receiver: Arc<Mutex<std::sync::mpsc::Receiver<Value>>>,
}

impl ChannelValue {
    /// Create a new unbuffered channel
    pub fn new() -> Self {
        let (tx, rx) = std::sync::mpsc::channel();
        ChannelValue {
            sender: tx,
            receiver: Arc::new(Mutex::new(rx)),
        }
    }

    /// Create a new buffered channel with the given capacity
    /// Note: Rust's mpsc doesn't support true buffering, so we just create a regular channel
    /// The capacity is ignored for simplicity
    pub fn with_buffer(_capacity: usize) -> Self {
        // For now, just create a regular unbounded channel
        // True buffering would require a different implementation
        Self::new()
    }

    /// Send a value through the channel
    pub fn send(&self, value: Value) -> Result<(), String> {
        self.sender
            .send(value)
            .map_err(|_| "channel closed".to_string())
    }

    /// Receive a value from the channel (blocking)
    pub fn recv(&self) -> Result<Value, String> {
        self.receiver
            .lock()
            .map_err(|_| "channel lock poisoned".to_string())?
            .recv()
            .map_err(|_| "channel closed".to_string())
    }

    /// Try to receive a value without blocking
    pub fn try_recv(&self) -> Option<Value> {
        self.receiver
            .lock()
            .ok()?
            .try_recv()
            .ok()
    }
}

impl Clone for ChannelValue {
    fn clone(&self) -> Self {
        ChannelValue {
            sender: self.sender.clone(),
            receiver: self.receiver.clone(),
        }
    }
}

impl PartialEq for ChannelValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.receiver, &other.receiver)
    }
}

/// Thread pool for parallel task execution
#[derive(Debug)]
pub struct ThreadPoolValue {
    workers: usize,
}

impl ThreadPoolValue {
    /// Create a new thread pool with the given number of workers
    pub fn new(workers: usize) -> Self {
        ThreadPoolValue { workers }
    }
}

impl Clone for ThreadPoolValue {
    fn clone(&self) -> Self {
        ThreadPoolValue {
            workers: self.workers,
        }
    }
}

impl PartialEq for ThreadPoolValue {
    fn eq(&self, other: &Self) -> bool {
        self.workers == other.workers
    }
}
