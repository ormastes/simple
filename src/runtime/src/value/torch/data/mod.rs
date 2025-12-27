//! PyTorch data loading module
//!
//! This module provides Dataset and DataLoader implementations for batch iteration,
//! following the handle-based registry pattern.
//!
//! Key components:
//! - Dataset: wraps tensors for indexing
//! - DataLoader: batch iteration with shuffle and drop_last options
//! - Registries: thread-safe storage for dataset/dataloader handles

#[cfg(feature = "pytorch")]
use parking_lot::Mutex;

#[cfg(feature = "pytorch")]
use std::collections::HashMap;

#[cfg(feature = "pytorch")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

// Re-export submodules
pub mod dataset;
pub mod dataloader;

// Re-export public types and functions
pub use dataset::*;
pub use dataloader::*;

// ============================================================================
// Registries
// ============================================================================

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    pub(crate) static ref DATASET_REGISTRY: Mutex<HashMap<u64, Arc<dataset::DatasetState>>> =
        Mutex::new(HashMap::new());
    pub(crate) static ref NEXT_DATASET_HANDLE: AtomicU64 = AtomicU64::new(1);

    pub(crate) static ref DATALOADER_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<dataloader::DataLoaderState>>>> =
        Mutex::new(HashMap::new());
    pub(crate) static ref NEXT_DATALOADER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
pub(crate) fn next_dataset_handle() -> u64 {
    NEXT_DATASET_HANDLE.fetch_add(1, Ordering::SeqCst)
}

#[cfg(feature = "pytorch")]
pub(crate) fn next_dataloader_handle() -> u64 {
    NEXT_DATALOADER_HANDLE.fetch_add(1, Ordering::SeqCst)
}
