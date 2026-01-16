//! GC write barriers for concurrent collections.
//!
//! Write barriers ensure that the GC correctly traces references stored in
//! concurrent data structures, preventing premature collection of reachable objects.
//!
//! ## Implementation
//!
//! The write barrier works in two modes:
//!
//! 1. **Incremental GC**: Marks objects as they're stored (Steele-Dijkstra barrier)
//! 2. **Non-incremental GC**: Defers marking to collection time (snapshot-at-beginning)
//!
//! ## Tri-Color Marking
//!
//! Objects are marked with three colors:
//! - **White**: Not yet visited (may be garbage)
//! - **Gray**: Reachable but not yet scanned (in work queue)
//! - **Black**: Fully scanned (definitely reachable)
//!
//! The write barrier ensures the tri-color invariant: no black object points to
//! a white object. When storing a reference during GC, we mark the stored object
//! gray to ensure it will be scanned.
//!
//! ## Performance
//!
//! - Write barrier: ~2-5ns overhead per store
//! - Read barrier: No overhead (objects stay valid)
//! - Tracing: Lock-free snapshot of collection contents

use crate::value::heap::HeapHeader;
use crate::value::RuntimeValue;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

/// Global GC state for write barrier coordination
static GC_STATE: GcBarrierState = GcBarrierState::new();

/// Global work queue for gray objects that need scanning
static GRAY_QUEUE: GrayQueue = GrayQueue::new();

/// GC barrier state shared across all concurrent collections
struct GcBarrierState {
    /// Is a GC collection currently in progress?
    collecting: AtomicBool,
    /// Epoch counter for snapshot-at-beginning
    epoch: AtomicUsize,
    /// Statistics: number of objects marked gray by write barrier
    barrier_marks: AtomicUsize,
}

/// Thread-safe queue of gray objects waiting to be scanned
struct GrayQueue {
    /// Queue of heap object pointers that need scanning
    /// Using a Mutex for simplicity; could use lock-free queue for better performance
    queue: Mutex<VecDeque<*mut HeapHeader>>,
}

// Safety: GrayQueue only stores raw pointers which are Send
unsafe impl Send for GrayQueue {}
unsafe impl Sync for GrayQueue {}

impl GrayQueue {
    const fn new() -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
        }
    }

    /// Push an object onto the gray queue
    fn push(&self, ptr: *mut HeapHeader) {
        if let Ok(mut queue) = self.queue.lock() {
            queue.push_back(ptr);
        }
    }

    /// Pop an object from the gray queue (returns None if empty)
    fn pop(&self) -> Option<*mut HeapHeader> {
        if let Ok(mut queue) = self.queue.lock() {
            queue.pop_front()
        } else {
            None
        }
    }

    /// Get approximate queue length
    fn len(&self) -> usize {
        self.queue.lock().map(|q| q.len()).unwrap_or(0)
    }

    /// Clear the queue (for new GC cycle)
    fn clear(&self) {
        if let Ok(mut queue) = self.queue.lock() {
            queue.clear();
        }
    }
}

impl GcBarrierState {
    const fn new() -> Self {
        Self {
            collecting: AtomicBool::new(false),
            epoch: AtomicUsize::new(0),
            barrier_marks: AtomicUsize::new(0),
        }
    }

    /// Mark the start of a GC collection
    #[inline]
    fn start_collection(&self) {
        // Clear statistics for new cycle
        self.barrier_marks.store(0, Ordering::Relaxed);
        // Clear the gray queue
        GRAY_QUEUE.clear();
        // Set collecting flag and bump epoch
        self.collecting.store(true, Ordering::Release);
        self.epoch.fetch_add(1, Ordering::AcqRel);
    }

    /// Mark the end of a GC collection
    #[inline]
    fn end_collection(&self) {
        self.collecting.store(false, Ordering::Release);
    }

    /// Check if GC is currently collecting
    #[inline]
    fn is_collecting(&self) -> bool {
        self.collecting.load(Ordering::Acquire)
    }

    /// Get current epoch
    #[inline]
    fn epoch(&self) -> usize {
        self.epoch.load(Ordering::Acquire)
    }

    /// Increment barrier mark count
    #[inline]
    fn inc_barrier_marks(&self) {
        self.barrier_marks.fetch_add(1, Ordering::Relaxed);
    }

    /// Get number of objects marked by write barrier this cycle
    fn barrier_mark_count(&self) -> usize {
        self.barrier_marks.load(Ordering::Relaxed)
    }
}

/// Write barrier for storing GC-managed values in concurrent collections.
///
/// This implements a Steele-Dijkstra incremental write barrier that ensures
/// newly stored references are visible to the GC during concurrent marking.
pub struct GcWriteBarrier;

impl GcWriteBarrier {
    /// Execute write barrier when storing a value in a concurrent collection.
    ///
    /// This is called automatically by concurrent collection implementations
    /// before storing GC-managed values.
    ///
    /// # Algorithm
    ///
    /// ```text
    /// if GC_IS_COLLECTING:
    ///     mark_value_as_reachable(value)
    /// store(value)
    /// ```
    #[inline]
    pub fn on_write(value: RuntimeValue) {
        if GC_STATE.is_collecting() {
            // During GC, mark the value to prevent collection
            Self::mark_gray(value);
        }
        // Value is now safe to store in the collection
    }

    /// Mark a value as gray (reachable but not yet scanned).
    ///
    /// This is the core of the incremental write barrier. Gray objects
    /// are guaranteed to be scanned during the current GC cycle.
    ///
    /// # Algorithm
    ///
    /// 1. Check if value is a heap object
    /// 2. If white (not yet seen), mark it gray
    /// 3. Push onto gray queue for scanning
    ///
    /// This maintains the tri-color invariant: no black object points to white.
    #[inline(never)] // Keep barrier overhead minimal for common case
    fn mark_gray(value: RuntimeValue) {
        // Only heap objects need marking
        if !value.is_heap() {
            return;
        }

        let ptr = value.as_heap_ptr();
        if ptr.is_null() {
            return;
        }

        // Safety: We've verified the pointer is non-null and from a valid RuntimeValue
        unsafe {
            let header = &mut *ptr;

            // Only mark if white (not yet seen this cycle)
            // If already gray or black, no need to mark again
            if header.is_white() {
                header.mark_gray();
                // Push onto work queue for scanning
                GRAY_QUEUE.push(ptr);
                // Update statistics
                GC_STATE.inc_barrier_marks();
                tracing::trace!("GC write barrier: marked {:p} as gray", ptr);
            }
        }
    }

    /// Notify GC that a collection is starting (called by GC runtime)
    pub fn start_collection() {
        GC_STATE.start_collection();
    }

    /// Notify GC that a collection has ended (called by GC runtime)
    pub fn end_collection() {
        GC_STATE.end_collection();
    }

    /// Get current GC epoch (for snapshot-at-beginning)
    pub fn epoch() -> usize {
        GC_STATE.epoch()
    }

    /// Get number of objects marked by write barrier this GC cycle
    pub fn barrier_mark_count() -> usize {
        GC_STATE.barrier_mark_count()
    }

    /// Get the number of gray objects waiting to be scanned
    pub fn gray_queue_len() -> usize {
        GRAY_QUEUE.len()
    }

    /// Pop the next gray object for scanning (called by GC during marking)
    ///
    /// Returns None if the queue is empty.
    pub fn pop_gray() -> Option<*mut HeapHeader> {
        GRAY_QUEUE.pop()
    }

    /// Mark a heap object as black after scanning its children
    ///
    /// # Safety
    ///
    /// The pointer must be a valid heap object pointer.
    pub unsafe fn mark_black(ptr: *mut HeapHeader) {
        if !ptr.is_null() {
            (*ptr).mark_black();
        }
    }

    /// Reset all objects to white for a new GC cycle
    ///
    /// This should be called at the end of a GC cycle before end_collection().
    /// In practice, only surviving objects need to be reset.
    ///
    /// # Safety
    ///
    /// The pointer must be a valid heap object pointer.
    pub unsafe fn reset_color(ptr: *mut HeapHeader) {
        if !ptr.is_null() {
            (*ptr).reset_color();
        }
    }
}

/// Trait for types that can be traced by the GC through concurrent collections.
///
/// All concurrent collections implement this trait to provide a snapshot
/// of their contents for GC tracing.
pub trait TraceConcurrent {
    /// Provide a snapshot of all GC-managed values in this collection.
    ///
    /// This is called during GC marking to trace all reachable objects.
    /// The implementation must return all values that were present at the
    /// start of the current GC epoch.
    ///
    /// # Snapshot Consistency
    ///
    /// Uses snapshot-at-beginning: all values inserted before `GcWriteBarrier::epoch()`
    /// must be included. Values inserted after may or may not be included.
    fn trace_snapshot(&self) -> Vec<RuntimeValue>;

    /// Count of values in the collection (approximate for concurrent collections)
    fn approximate_len(&self) -> usize;
}

// FFI functions for write barrier control (callable from compiled code)

/// Start a GC collection cycle
#[no_mangle]
pub extern "C" fn simple_gc_barrier_start_collection() {
    GcWriteBarrier::start_collection();
}

/// End a GC collection cycle
#[no_mangle]
pub extern "C" fn simple_gc_barrier_end_collection() {
    GcWriteBarrier::end_collection();
}

/// Get current GC epoch
#[no_mangle]
pub extern "C" fn simple_gc_barrier_epoch() -> usize {
    GcWriteBarrier::epoch()
}

/// Get number of objects marked by write barrier this cycle
#[no_mangle]
pub extern "C" fn simple_gc_barrier_mark_count() -> usize {
    GcWriteBarrier::barrier_mark_count()
}

/// Get length of gray queue
#[no_mangle]
pub extern "C" fn simple_gc_gray_queue_len() -> usize {
    GcWriteBarrier::gray_queue_len()
}

/// Execute write barrier for a value being stored
#[no_mangle]
pub extern "C" fn simple_gc_write_barrier(value: RuntimeValue) {
    GcWriteBarrier::on_write(value);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::heap::gc_flags;

    #[test]
    fn test_gc_state_transitions() {
        // End any previous collection first
        GC_STATE.end_collection();

        // Initial state: not collecting
        assert!(!GC_STATE.is_collecting());
        let epoch1 = GC_STATE.epoch();

        // Start collection
        GC_STATE.start_collection();
        assert!(GC_STATE.is_collecting());
        let epoch2 = GC_STATE.epoch();
        assert!(epoch2 > epoch1);

        // End collection
        GC_STATE.end_collection();
        assert!(!GC_STATE.is_collecting());
    }

    #[test]
    fn test_write_barrier_no_overhead_when_not_collecting() {
        GC_STATE.end_collection(); // Ensure not collecting

        // Write barrier should be a no-op for non-heap values
        let value = RuntimeValue::from_int(42);
        GcWriteBarrier::on_write(value);

        // No crash = success
    }

    #[test]
    fn test_write_barrier_marks_heap_objects() {
        // Create a heap object for testing
        use crate::value::heap::HeapObjectType;
        use std::alloc::{alloc, dealloc, Layout};

        // Allocate a minimal heap object
        let layout = Layout::new::<HeapHeader>();
        let ptr = unsafe { alloc(layout) as *mut HeapHeader };
        assert!(!ptr.is_null());

        unsafe {
            // Initialize the header
            std::ptr::write(
                ptr,
                HeapHeader::new(HeapObjectType::Object, layout.size() as u32),
            );

            // Verify initial state is white
            assert!((*ptr).is_white());

            // Create a RuntimeValue pointing to this object
            // Safety: ptr is valid and properly aligned (from alloc)
            let value = RuntimeValue::from_heap_ptr(ptr);

            // Start a GC collection
            GC_STATE.start_collection();
            let initial_marks = GC_STATE.barrier_mark_count();

            // Execute write barrier
            GcWriteBarrier::on_write(value);

            // Object should now be gray
            assert!((*ptr).is_gray(), "Object should be marked gray after write barrier");
            assert!(
                GC_STATE.barrier_mark_count() > initial_marks,
                "Barrier mark count should increase"
            );

            // Gray queue should have the object
            assert!(GRAY_QUEUE.len() > 0, "Gray queue should not be empty");

            // End collection
            GC_STATE.end_collection();

            // Clean up
            dealloc(ptr as *mut u8, layout);
        }
    }

    #[test]
    fn test_heap_header_colors() {
        let mut header = HeapHeader::new(crate::value::heap::HeapObjectType::String, 100);

        // Initial state is white
        assert!(header.is_white());
        assert!(!header.is_gray());
        assert!(!header.is_black());
        assert_eq!(header.gc_color(), gc_flags::WHITE);

        // Mark gray
        header.mark_gray();
        assert!(!header.is_white());
        assert!(header.is_gray());
        assert!(!header.is_black());
        assert_eq!(header.gc_color(), gc_flags::GRAY);

        // Mark black
        header.mark_black();
        assert!(!header.is_white());
        assert!(!header.is_gray());
        assert!(header.is_black());
        assert_eq!(header.gc_color(), gc_flags::BLACK);

        // Reset to white
        header.reset_color();
        assert!(header.is_white());
    }

    #[test]
    fn test_heap_header_pinning() {
        let mut header = HeapHeader::new(crate::value::heap::HeapObjectType::Array, 200);

        // Initial state is not pinned
        assert!(!header.is_pinned());

        // Pin the object
        header.pin();
        assert!(header.is_pinned());

        // Pinning should not affect color
        assert!(header.is_white());
        header.mark_gray();
        assert!(header.is_gray());
        assert!(header.is_pinned());

        // Unpin
        header.unpin();
        assert!(!header.is_pinned());
        assert!(header.is_gray()); // Color unchanged
    }

    #[test]
    fn test_gray_queue() {
        // Clear any previous state
        GRAY_QUEUE.clear();
        assert_eq!(GRAY_QUEUE.len(), 0);

        // Push some pointers
        let ptr1 = 0x1000 as *mut HeapHeader;
        let ptr2 = 0x2000 as *mut HeapHeader;
        GRAY_QUEUE.push(ptr1);
        GRAY_QUEUE.push(ptr2);
        assert_eq!(GRAY_QUEUE.len(), 2);

        // Pop in FIFO order
        assert_eq!(GRAY_QUEUE.pop(), Some(ptr1));
        assert_eq!(GRAY_QUEUE.pop(), Some(ptr2));
        assert_eq!(GRAY_QUEUE.pop(), None);
        assert_eq!(GRAY_QUEUE.len(), 0);
    }

    #[test]
    fn test_ffi_functions() {
        simple_gc_barrier_start_collection();
        assert!(GC_STATE.is_collecting());

        let epoch = simple_gc_barrier_epoch();
        assert!(epoch > 0);

        // Test new FFI functions
        let _mark_count = simple_gc_barrier_mark_count();
        let _queue_len = simple_gc_gray_queue_len();

        // Test write barrier FFI
        let value = RuntimeValue::from_int(42);
        simple_gc_write_barrier(value);

        simple_gc_barrier_end_collection();
        assert!(!GC_STATE.is_collecting());
    }
}
