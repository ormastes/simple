use std::fmt;
use std::sync::Arc;

use abfall::{GcContext, Heap};
use simple_common::gc::GcAllocator;
use tracing::instrument;

/// Event emitted by the GC runtime when logging is enabled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GcLogEventKind {
    Allocation,
    CollectionStart,
    CollectionEnd,
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
        }
    }
}

type LogSink = Arc<dyn Fn(GcLogEvent) + Send + Sync>;

/// Thin wrapper around the Abfall GC with optional structured logging.
pub struct GcRuntime {
    ctx: GcContext,
    log: Option<LogSink>,
}

impl Default for GcRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl GcRuntime {
    /// Create a GC runtime with default options and no logging.
    pub fn new() -> Self {
        Self::with_options(GcOptions::new(), None)
    }

    /// Create a GC runtime with custom options.
    pub fn with_options(options: GcOptions, log: Option<LogSink>) -> Self {
        let ctx = GcContext::with_options(options);
        Self { ctx, log }
    }

    /// Create a GC runtime that emits structured logs to the provided sink.
    pub fn with_logger(logger: impl Fn(GcLogEvent) + Send + Sync + 'static) -> Self {
        Self::with_options(GcOptions::new(), Some(Arc::new(logger)))
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
        let root = self.ctx.allocate(bytes.to_vec());
        let ptr: *const Vec<u8> = root.as_ptr().as_ptr();
        ptr as usize
    }

    fn collect(&self) {
        self.collect("ffi");
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
