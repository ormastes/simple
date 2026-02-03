// Memory module
//
// GC has been migrated to Simple implementation (src/app/gc/)
// Rust GC code removed - use Simple GC instead

// Deleted files (migrated to Simple):
// - gc.rs -> src/app/gc/core.spl (compatibility stubs below)
// - gcless.rs -> removed
// - no_gc.rs -> removed (compatibility stubs below)

use std::sync::Mutex;

// GC compatibility stubs
pub mod gc;
pub mod no_gc;

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
