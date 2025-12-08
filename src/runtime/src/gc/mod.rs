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
