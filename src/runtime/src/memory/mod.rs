pub mod gc;
pub mod gcless;
pub mod no_gc;

// Re-export GC types for downstream convenience.
pub use gc::{GcLogEvent, GcLogEventKind, GcRuntime};
pub use gcless::GclessAllocator;
pub use no_gc::NoGcAllocator;

use std::sync::Mutex;

/// Helper function to allocate bytes and track in an allocation list.
/// This is shared between NoGcAllocator and GclessAllocator.
#[inline]
pub(crate) fn alloc_bytes_tracked(bytes: &[u8], allocations: &Mutex<Vec<Box<[u8]>>>) -> usize {
    let mut buf = Vec::with_capacity(bytes.len());
    buf.extend_from_slice(bytes);
    let boxed: Box<[u8]> = buf.into_boxed_slice();
    let ptr = boxed.as_ptr() as usize;
    allocations.lock().unwrap().push(boxed);
    ptr
}
