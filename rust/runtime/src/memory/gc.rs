use std::fmt;
use std::sync::Arc;

use abfall::{GcContext, Heap};
use simple_common::gc::{AllocResult, GcAllocator, MemoryLimitConfig, MemoryLimitExceeded, MemoryTracker};
use tracing::instrument;

/// Event emitted by the GC runtime when logging is enabled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GcLogEventKind {
    Allocation,
    CollectionStart,
    CollectionEnd,
    MemoryLimitExceeded,
}

/// Structured GC log entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GcLogEvent {
    pub kind: GcLogEventKind,
    pub reason: Option<String>,
    pub bytes_in_use: usize,
}

impl fmt::Display for GcLogEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            GcLogEventKind::Allocation => write!(f, "gc:alloc bytes={}", self.bytes_in_use),
            GcLogEventKind::CollectionStart => write!(
                f,
                "gc:start reason={} bytes={}",
                self.reason.as_deref().unwrap_or("unknown"),
                self.bytes_in_use
            ),
            GcLogEventKind::CollectionEnd => write!(
                f,
                "gc:end reason={} bytes={}",
                self.reason.as_deref().unwrap_or("unknown"),
                self.bytes_in_use
            ),
            GcLogEventKind::MemoryLimitExceeded => write!(
                f,
                "gc:limit_exceeded reason={} bytes={}",
                self.reason.as_deref().unwrap_or("unknown"),
                self.bytes_in_use
            ),
        }
    }
}

type LogSink = Arc<dyn Fn(GcLogEvent) + Send + Sync>;

/// Tracks heap size after GC collections to detect possible memory leaks.
/// If heap grows >10% over N consecutive cycles, emits a warning.
struct LeakDetector {
    enabled: bool,
    post_gc_sizes: Vec<usize>,
    window_size: usize,
}

impl LeakDetector {
    fn new() -> Self {
        let enabled = std::env::var("SIMPLE_LEAK_DETECTION")
            .map(|v| matches!(v.to_lowercase().as_str(), "1" | "true" | "yes"))
            .unwrap_or(false);
        Self {
            enabled,
            post_gc_sizes: Vec::new(),
            window_size: 10,
        }
    }

    fn record_post_gc(&mut self, heap_bytes: usize) {
        if !self.enabled {
            return;
        }
        self.post_gc_sizes.push(heap_bytes);
        if self.post_gc_sizes.len() >= self.window_size {
            let first = self.post_gc_sizes[self.post_gc_sizes.len() - self.window_size];
            let last = heap_bytes;
            if first > 0 && last > first {
                let growth = (last - first) as f64 / first as f64;
                if growth > 0.10 {
                    tracing::warn!(
                        first_bytes = first,
                        last_bytes = last,
                        growth_pct = format!("{:.1}%", growth * 100.0),
                        window = self.window_size,
                        "Possible memory leak: heap grew {:.1}% over {} GC cycles",
                        growth * 100.0,
                        self.window_size,
                    );
                }
            }
        }
    }
}

/// Thin wrapper around the Abfall GC with optional structured logging and memory limits.
pub struct GcRuntime {
    ctx: GcContext,
    log: Option<LogSink>,
    /// Memory tracker for enforcing limits
    memory_tracker: MemoryTracker,
    /// Leak detector (opt-in via SIMPLE_LEAK_DETECTION=1)
    leak_detector: std::cell::RefCell<LeakDetector>,
}

impl Default for GcRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl GcRuntime {
    /// Create a GC runtime with default options, no logging, and default memory limit (1 GB).
    pub fn new() -> Self {
        Self::with_options(GcOptions::new(), None, MemoryLimitConfig::default())
    }

    /// Create a GC runtime with unlimited memory.
    pub fn unlimited() -> Self {
        Self::with_options(GcOptions::new(), None, MemoryLimitConfig::unlimited())
    }

    /// Create a GC runtime with custom options and memory limit.
    pub fn with_options(options: GcOptions, log: Option<LogSink>, memory_config: MemoryLimitConfig) -> Self {
        let ctx = GcContext::with_options(options);
        Self {
            ctx,
            log,
            memory_tracker: MemoryTracker::with_config(memory_config),
            leak_detector: std::cell::RefCell::new(LeakDetector::new()),
        }
    }

    /// Create a GC runtime with specific memory limit in bytes.
    pub fn with_memory_limit(limit_bytes: usize) -> Self {
        Self::with_options(GcOptions::new(), None, MemoryLimitConfig::with_limit(limit_bytes))
    }

    /// Create a GC runtime with memory limit in megabytes.
    pub fn with_memory_limit_mb(limit_mb: usize) -> Self {
        Self::with_options(GcOptions::new(), None, MemoryLimitConfig::with_limit_mb(limit_mb))
    }

    /// Create a GC runtime with memory limit in gigabytes.
    pub fn with_memory_limit_gb(limit_gb: usize) -> Self {
        Self::with_options(GcOptions::new(), None, MemoryLimitConfig::with_limit_gb(limit_gb))
    }

    /// Create a GC runtime that emits structured logs to the provided sink.
    pub fn with_logger(logger: impl Fn(GcLogEvent) + Send + Sync + 'static) -> Self {
        Self::with_options(GcOptions::new(), Some(Arc::new(logger)), MemoryLimitConfig::default())
    }

    /// Create a GC runtime with both logger and memory limit.
    pub fn with_logger_and_limit(
        logger: impl Fn(GcLogEvent) + Send + Sync + 'static,
        memory_config: MemoryLimitConfig,
    ) -> Self {
        Self::with_options(GcOptions::new(), Some(Arc::new(logger)), memory_config)
    }

    /// Create a GC runtime that prints verbose logs to stdout.
    pub fn verbose_stdout() -> Self {
        Self::with_logger(|event| {
            println!("{}", event);
        })
    }

    /// Access the underlying heap for advanced metrics.
    pub fn heap(&self) -> &Arc<Heap> {
        self.ctx.heap()
    }

    /// Current heap usage in bytes.
    pub fn heap_bytes(&self) -> usize {
        self.ctx.heap().bytes_allocated()
    }

    /// Get tracked memory usage (may differ from heap_bytes due to tracking granularity)
    pub fn tracked_memory(&self) -> usize {
        self.memory_tracker.current_bytes()
    }

    /// Get memory limit in bytes (0 if unlimited)
    pub fn memory_limit(&self) -> usize {
        self.memory_tracker.limit_bytes()
    }

    /// Check if memory is limited
    pub fn is_memory_limited(&self) -> bool {
        self.memory_tracker.is_limited()
    }

    /// Get memory usage as percentage of limit
    pub fn memory_usage_percent(&self) -> f64 {
        self.memory_tracker.usage_percent()
    }

    /// Allocate data on the GC heap, emitting a log entry if enabled.
    pub fn allocate<T: Trace>(&self, data: T) -> GcRoot<T> {
        let root = self.ctx.allocate(data);
        self.log_event(GcLogEvent {
            kind: GcLogEventKind::Allocation,
            reason: None,
            bytes_in_use: self.heap_bytes(),
        });
        root
    }

    /// Try to allocate data, returning error if memory limit exceeded.
    pub fn try_allocate<T: Trace>(&self, data: T, size_hint: usize) -> AllocResult<GcRoot<T>> {
        // Check memory limit
        self.memory_tracker.try_allocate(size_hint)?;

        let root = self.ctx.allocate(data);
        self.log_event(GcLogEvent {
            kind: GcLogEventKind::Allocation,
            reason: None,
            bytes_in_use: self.heap_bytes(),
        });
        Ok(root)
    }

    /// Force a collection and log start/end markers.
    #[instrument(skip(self), fields(reason))]
    pub fn collect(&self, reason: &str) -> usize {
        let before = self.heap_bytes();
        self.log_event(GcLogEvent {
            kind: GcLogEventKind::CollectionStart,
            reason: Some(reason.to_string()),
            bytes_in_use: before,
        });
        let after = self.ctx.heap().force_collect();
        self.log_event(GcLogEvent {
            kind: GcLogEventKind::CollectionEnd,
            reason: Some(reason.to_string()),
            bytes_in_use: after,
        });

        // Update memory tracker to reflect post-collection state
        // This resets the tracker to match actual heap usage
        let freed = before.saturating_sub(after);
        if freed > 0 {
            self.memory_tracker.deallocate(freed);
        }

        // Leak detection: record post-GC heap size
        self.leak_detector.borrow_mut().record_post_gc(after);

        after
    }

    fn log_event(&self, event: GcLogEvent) {
        if let Some(log) = &self.log {
            log(event);
        }
    }
}

// Re-export common GC traits/types so callers don't need to depend on abfall directly.
pub use abfall::{GcOptions, GcRoot, Trace};

impl GcAllocator for GcRuntime {
    fn alloc_bytes(&self, bytes: &[u8]) -> usize {
        // Try to allocate with limit checking, panic on failure
        match self.try_alloc_bytes(bytes) {
            Ok(ptr) => ptr,
            Err(e) => panic!("{}", e),
        }
    }

    fn try_alloc_bytes(&self, bytes: &[u8]) -> AllocResult<usize> {
        // Check memory limit before allocating
        self.memory_tracker.try_allocate(bytes.len())?;

        let root = self.ctx.allocate(bytes.to_vec());
        let ptr: *const Vec<u8> = root.as_ptr().as_ptr();

        self.log_event(GcLogEvent {
            kind: GcLogEventKind::Allocation,
            reason: None,
            bytes_in_use: self.heap_bytes(),
        });

        Ok(ptr as usize)
    }

    fn collect(&self) {
        self.collect("ffi");
    }

    fn memory_usage(&self) -> usize {
        self.tracked_memory()
    }

    fn memory_limit(&self) -> usize {
        self.memory_tracker.limit_bytes()
    }
}

// ============================================================================
// Unique Pointer GC Root Registration
// ============================================================================
//
// Unique pointers are manually allocated (not through GC), but they may contain
// references to GC-managed values. To prevent those nested values from being
// collected, unique pointers register as GC roots.

use std::cell::RefCell;

thread_local! {
    /// Registry of unique pointer addresses that contain GC-traceable values
    static UNIQUE_ROOTS: RefCell<Vec<*mut u8>> = const { RefCell::new(Vec::new()) };
}

/// Register a unique pointer as a GC root.
/// Called when a unique pointer is created with a value that contains heap references.
pub fn register_unique_root(ptr: *mut u8) {
    UNIQUE_ROOTS.with(|roots| {
        roots.borrow_mut().push(ptr);
    });
}

/// Unregister a unique pointer from GC roots.
/// Called when a unique pointer is deallocated.
pub fn unregister_unique_root(ptr: *mut u8) {
    UNIQUE_ROOTS.with(|roots| {
        roots.borrow_mut().retain(|&p| p != ptr);
    });
}

/// Get all registered unique roots for GC tracing.
/// Returns a snapshot of currently registered unique pointer addresses.
pub fn get_unique_roots() -> Vec<*mut u8> {
    UNIQUE_ROOTS.with(|roots| roots.borrow().clone())
}

/// Get the count of registered unique roots.
pub fn unique_root_count() -> usize {
    UNIQUE_ROOTS.with(|roots| roots.borrow().len())
}

// ============================================================================
// Shared Pointer GC Root Registration
// ============================================================================
//
// Shared pointers are reference-counted and manually allocated. Like unique
// pointers, they may contain references to GC-managed values and need to
// register as GC roots.

thread_local! {
    /// Registry of shared pointer addresses that contain GC-traceable values
    static SHARED_ROOTS: RefCell<Vec<*mut u8>> = const { RefCell::new(Vec::new()) };
}

/// Register a shared pointer as a GC root.
/// Called when a shared pointer is created with a value that contains heap references.
pub fn register_shared_root(ptr: *mut u8) {
    SHARED_ROOTS.with(|roots| {
        roots.borrow_mut().push(ptr);
    });
}

/// Unregister a shared pointer from GC roots.
/// Called when a shared pointer's reference count drops to zero.
pub fn unregister_shared_root(ptr: *mut u8) {
    SHARED_ROOTS.with(|roots| {
        roots.borrow_mut().retain(|&p| p != ptr);
    });
}

/// Get all registered shared roots for GC tracing.
pub fn get_shared_roots() -> Vec<*mut u8> {
    SHARED_ROOTS.with(|roots| roots.borrow().clone())
}

/// Get the count of registered shared roots.
pub fn shared_root_count() -> usize {
    SHARED_ROOTS.with(|roots| roots.borrow().len())
}
