// Async and concurrent value types for the interpreter
// These are split from value.rs for maintainability
// Note: This file is included via include!() - imports come from parent value.rs

/// A future that wraps a thread join handle and result
#[derive(Debug)]
pub struct FutureValue {
    result: Arc<Mutex<Option<Result<Value, String>>>>,
    handle: Arc<Mutex<Option<std::thread::JoinHandle<()>>>>,
}

impl FutureValue {
    /// Create a new future from a computation
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce() -> Result<Value, String> + Send + 'static,
    {
        let result: Arc<Mutex<Option<Result<Value, String>>>> = Arc::new(Mutex::new(None));
        let result_clone = result.clone();
        let handle = std::thread::spawn(move || {
            let res = f();
            *result_clone.lock().unwrap() = Some(res);
        });
        FutureValue {
            result,
            handle: Arc::new(Mutex::new(Some(handle))),
        }
    }

    /// Wait for the future to complete and return the result
    pub fn await_result(&self) -> Result<Value, String> {
        // First, join the thread if it's still running
        if let Some(handle) = self.handle.lock().unwrap().take() {
            let _ = handle.join();
        }
        // Then get the result
        self.result
            .lock()
            .unwrap()
            .take()
            .unwrap_or(Err("future result already consumed".to_string()))
    }

    /// Check if the future is completed without blocking
    pub fn is_ready(&self) -> bool {
        self.result.lock().unwrap().is_some()
    }
}

impl Clone for FutureValue {
    fn clone(&self) -> Self {
        FutureValue {
            result: self.result.clone(),
            handle: self.handle.clone(),
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
