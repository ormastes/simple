//! Common types and registries for file I/O operations
//!
//! This module provides shared infrastructure for memory-mapped file handling:
//! - MmapRegion struct for tracking mapped memory regions
//! - Global registry for active mappings
//! - Thread-safety implementations for concurrent access

use std::sync::Mutex;

/// Memory-mapped region handle
///
/// Represents a single memory-mapped region with its base pointer and size.
/// Used to track active mappings and facilitate cleanup.
pub(super) struct MmapRegion {
    /// Base pointer to the memory-mapped region
    pub ptr: *mut u8,
    /// Size of the mapped region in bytes
    pub size: usize,
}

impl MmapRegion {
    /// Create a new MmapRegion
    #[inline]
    pub(super) fn new(ptr: *mut u8, size: usize) -> Self {
        MmapRegion { ptr, size }
    }
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
pub(super) static MMAP_REGISTRY: std::sync::OnceLock<Mutex<Vec<MmapRegion>>> =
    std::sync::OnceLock::new();

/// Initialize the MMAP_REGISTRY
#[inline]
pub(super) fn init_mmap_registry() {
    let _ = MMAP_REGISTRY.get_or_init(|| Mutex::new(Vec::new()));
}

/// Get the MMAP_REGISTRY, initializing it if necessary
#[inline]
pub(super) fn get_mmap_registry() -> &'static Mutex<Vec<MmapRegion>> {
    MMAP_REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}
