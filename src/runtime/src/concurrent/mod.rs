//! Concurrent collections with GC support.
//!
//! This module provides thread-safe data structures that integrate with the GC
//! through write barriers, ensuring proper object tracing during concurrent access.
//!
//! ## Features (#1108-#1112)
//!
//! - GC write barriers for concurrent collections (#1108)
//! - ConcurrentMap[K, V] with GC objects (#1109)
//! - ConcurrentQueue[T] with GC objects (#1110)
//! - ConcurrentStack[T] with GC objects (#1111)
//! - Object tracing through collection handles (#1112)
//!
//! ## Architecture
//!
//! All concurrent collections use:
//! - **mimalloc**: Fast thread-local allocator
//! - **dashmap**: Lock-free concurrent hash map (alternative to libcuckoo/libcds)
//! - **crossbeam**: Lock-free queues and stacks (alternative to moodycamel)
//! - **GC write barriers**: Ensures GC traces references correctly
//!
//! ## Write Barriers
//!
//! When storing a GC-managed object in a concurrent collection, the write barrier:
//! 1. Notifies the GC that a new reference exists
//! 2. Ensures the referenced object is marked during collection
//! 3. Prevents premature collection of reachable objects
//!
//! ## Example
//!
//! ```ignore
//! use runtime::concurrent::{ConcurrentQueue, ConcurrentMap};
//! use runtime::value::RuntimeValue;
//!
//! // Create concurrent queue with GC-managed values
//! let queue = ConcurrentQueue::new();
//! queue.push(RuntimeValue::from_string("hello"));
//!
//! // Create concurrent map with GC-managed keys/values
//! let map = ConcurrentMap::new();
//! map.insert(
//!     RuntimeValue::from_string("key"),
//!     RuntimeValue::from_string("value")
//! );
//! ```

pub mod gc_barrier;
pub mod map;
pub mod queue;
pub mod stack;

// Re-export types
pub use gc_barrier::{GcWriteBarrier, TraceConcurrent};
pub use map::ConcurrentMap;
pub use queue::ConcurrentQueue;
pub use stack::ConcurrentStack;

// Re-export FFI functions from submodules
pub use gc_barrier::{simple_gc_barrier_end_collection, simple_gc_barrier_epoch, simple_gc_barrier_start_collection};
pub use map::{
    simple_concurrent_map_clear, simple_concurrent_map_contains_key, simple_concurrent_map_free,
    simple_concurrent_map_get, simple_concurrent_map_insert, simple_concurrent_map_is_empty, simple_concurrent_map_len,
    simple_concurrent_map_new, simple_concurrent_map_remove, simple_concurrent_map_with_capacity,
};
pub use queue::{
    simple_concurrent_queue_free, simple_concurrent_queue_is_empty, simple_concurrent_queue_len,
    simple_concurrent_queue_new, simple_concurrent_queue_push, simple_concurrent_queue_try_pop,
};
pub use stack::{
    simple_concurrent_stack_free, simple_concurrent_stack_is_empty, simple_concurrent_stack_len,
    simple_concurrent_stack_new, simple_concurrent_stack_push, simple_concurrent_stack_try_pop,
};
