//! File I/O runtime functions - Mold-inspired optimizations
//!
//! Provides native implementations for:
//! - Memory-mapped file operations (mmap)
//! - File I/O hints (fadvise)
//! - Zero-copy operations (sendfile, copy_file_range)
//! - Low-level system call wrappers (syscalls)
//! - File operations (open, close, read, write)
//! - Process management (spawn, wait, kill)

pub mod common;
pub mod fadvise;
pub mod mmap;
pub mod zerocopy;
pub mod file_ops;
pub mod process;
pub mod async_file;
pub mod syscalls;

// Re-export fadvise functions
pub use fadvise::{
    native_fadvise_sequential, native_fadvise_random,
    native_fadvise_willneed, native_fadvise_dontneed,
};

// Re-export mmap functions
pub use mmap::{
    native_mmap_create_shared, native_mmap_create,
    native_mmap_read, native_mmap_unmap,
};

// Re-export zero-copy functions
pub use zerocopy::{
    native_sendfile, native_copy_file_range,
};

// Re-export file operations
pub use file_ops::{
    native_fs_open, native_file_read, native_file_write,
    native_file_close, native_file_flush, native_file_seek,
    native_file_sync,
};

// Re-export process management functions
pub use process::{
    native_spawn_worker, native_process_wait, native_process_is_alive,
    native_process_kill, native_path_resolve,
};

// Re-export async file functions
pub use async_file::{
    native_async_file_create, native_async_file_start_loading,
    native_async_file_is_ready, native_async_file_get_state,
    native_async_file_wait, async_yield, FileLoadState,
};

// Re-export low-level syscall wrappers
pub use syscalls::{
    sys_mmap, sys_munmap, sys_madvise,
    sys_open, sys_close,
    sys_file_size, sys_file_exists,
};

/// Memory-mapped region handle
///
/// Represents a single memory-mapped region with its base pointer and size.
/// Used to track active mappings and facilitate cleanup.
pub struct MmapRegion {
    /// Base pointer to the memory-mapped region
    pub ptr: *mut u8,
    /// Size of the mapped region in bytes
    pub size: usize,
}

// SAFETY: MmapRegion only stores raw pointers from mmap which are thread-safe
// The pointer itself can be shared across threads as it points to memory-mapped pages.
// The kernel ensures visibility of updates across processes via cache coherency.
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

/// Global registry for active memory-mapped regions
///
/// Maintains a list of all currently mapped regions for lifecycle management.
/// In production, this should be replaced with a thread-local variant to reduce
/// contention on the global mutex.
///
/// # Thread Safety
/// Protected by a Mutex for safe concurrent access from multiple threads.
use std::sync::Mutex;
lazy_static::lazy_static! {
    pub static ref MMAP_REGISTRY: Mutex<Vec<MmapRegion>> = Mutex::new(Vec::new());
}
