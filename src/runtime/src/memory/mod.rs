pub mod gc;
pub mod no_gc;

// Re-export GC types for downstream convenience.
pub use gc::{GcLogEvent, GcLogEventKind, GcRuntime};
pub use no_gc::NoGcAllocator;
