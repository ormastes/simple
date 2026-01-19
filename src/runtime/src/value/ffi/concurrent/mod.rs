//! Concurrent data structures FFI.
//!
//! Provides thread-safe data structures for concurrent programming in Simple.
//! All structures use Mutex-based synchronization for safety and simplicity.
//!
//! ## Available Structures
//!
//! - **Arena** (`arena`) - Bump allocator for fast temporary allocations
//! - **ConcurrentMap** (`map`) - Thread-safe key-value map
//! - **ConcurrentQueue** (`queue`) - Thread-safe FIFO queue
//! - **ConcurrentStack** (`stack`) - Thread-safe LIFO stack
//! - **ResourcePool** (`pool`) - Bounded resource pool for reuse
//! - **ThreadLocalStorage** (`tls`) - Thread-safe storage with u64 keys
//!
//! ## Thread Safety
//!
//! All structures are safe to use from multiple threads concurrently.
//! They use Mutex internally, which is suitable for moderate contention.
//! For high-contention scenarios, consider lock-free alternatives.
//!
//! ## Usage Pattern
//!
//! All structures follow the same pattern:
//! 1. Create: `rt_xxx_new(...)`
//! 2. Use: Various operations specific to the structure
//! 3. Free: `rt_xxx_free(handle)`
//!
//! Handles are unique identifiers (i64) that reference the structure.

pub mod arena;
pub mod map;
pub mod pool;
pub mod queue;
pub mod stack;
pub mod tls;

// Re-export all concurrent data structure functions
pub use arena::*;
pub use map::*;
pub use pool::*;
pub use queue::*;
pub use stack::*;
pub use tls::*;
