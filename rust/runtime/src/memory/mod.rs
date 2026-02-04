pub mod gc;
pub mod gcless;
pub mod no_gc;

// Re-export GC types for downstream convenience.
pub use gc::{GcLogEvent, GcLogEventKind, GcRuntime};
pub use gcless::GclessAllocator;
pub use no_gc::NoGcAllocator;

// Re-export memory limit types from common
pub use simple_common::gc::{AllocResult, MemoryLimitConfig, MemoryLimitExceeded, MemoryTracker, DEFAULT_MEMORY_LIMIT};

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

/// Helper function to allocate bytes with memory limit tracking.
/// Returns error if memory limit would be exceeded.
#[inline]
pub(crate) fn alloc_bytes_tracked_with_limit(
    bytes: &[u8],
    allocations: &Mutex<Vec<Box<[u8]>>>,
    tracker: &MemoryTracker,
) -> AllocResult<usize> {
    // Check memory limit before allocating
    tracker.try_allocate(bytes.len())?;

    let mut buf = Vec::with_capacity(bytes.len());
    buf.extend_from_slice(bytes);
    let boxed: Box<[u8]> = buf.into_boxed_slice();
    let ptr = boxed.as_ptr() as usize;
    allocations.lock().unwrap().push(boxed);
    Ok(ptr)
}
