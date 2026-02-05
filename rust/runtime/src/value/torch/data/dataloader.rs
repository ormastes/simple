//! PyTorch DataLoader implementations
//!
//! This module provides DataLoader for batch iteration over datasets,
//! with support for shuffling and dropping incomplete batches.

#[cfg(feature = "pytorch")]
use tch::Tensor;

#[cfg(feature = "pytorch")]
use parking_lot::Mutex;

#[cfg(feature = "pytorch")]
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use super::super::{TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::dataset::{rt_torch_dataset_len, DatasetState};

#[cfg(feature = "pytorch")]
use super::{next_dataloader_handle, DATALOADER_REGISTRY, DATASET_REGISTRY};

use crate::value::torch::TorchFfiError;

// ============================================================================
// DataLoader Types
// ============================================================================

/// DataLoader state for batching and iteration
#[cfg(feature = "pytorch")]
#[derive(Debug)]
pub struct DataLoaderState {
    pub(crate) dataset: u64, // Dataset handle
    pub(crate) batch_size: usize,
    pub(crate) shuffle: bool,
    pub(crate) drop_last: bool,
    pub(crate) current_index: usize,
    pub(crate) indices: Vec<i64>, // Shuffled indices for current epoch
    pub(crate) num_samples: i64,
}

// ============================================================================
// DataLoader FFI Functions
// ============================================================================

/// Create a DataLoader for batch iteration
/// batch_size: number of samples per batch
/// shuffle: 1 to shuffle, 0 for sequential
/// drop_last: 1 to drop incomplete last batch, 0 to keep it
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_new(dataset_handle: u64, batch_size: i64, shuffle: i32, drop_last: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if batch_size <= 0 {
            return 0;
        }

        let num_samples = rt_torch_dataset_len(dataset_handle);
        if num_samples <= 0 {
            return 0;
        }

        // Create initial indices (0..num_samples)
        let mut indices: Vec<i64> = (0..num_samples).collect();

        // Shuffle if requested
        if shuffle != 0 {
            use rand::seq::SliceRandom;
            let mut rng = rand::thread_rng();
            indices.shuffle(&mut rng);
        }

        let state = DataLoaderState {
            dataset: dataset_handle,
            batch_size: batch_size as usize,
            shuffle: shuffle != 0,
            drop_last: drop_last != 0,
            current_index: 0,
            indices,
            num_samples,
        };

        let handle = next_dataloader_handle();
        DATALOADER_REGISTRY.lock().insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_dataloader_new: dataset={} batch_size={} shuffle={} -> loader={}",
            dataset_handle,
            batch_size,
            shuffle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (dataset_handle, batch_size, shuffle, drop_last);
        0
    }
}

/// Get next batch from dataloader
/// Returns handle to a batch tensor (stacked features), or 0 if iteration complete
/// The corresponding labels are at returned_handle + 1
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_next(dataloader_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let loader_registry = DATALOADER_REGISTRY.lock();
        let Some(loader) = loader_registry.get(&dataloader_handle).cloned() else {
            return 0;
        };
        drop(loader_registry);

        let mut state = loader.lock();

        // Check if iteration is complete
        if state.current_index >= state.num_samples as usize {
            return 0;
        }

        // Determine batch end
        let batch_end = std::cmp::min(state.current_index + state.batch_size, state.num_samples as usize);

        // Check if we should drop last incomplete batch
        if state.drop_last && (batch_end - state.current_index) < state.batch_size {
            state.current_index = state.num_samples as usize; // Mark as done
            return 0;
        }

        // Collect batch indices
        let batch_indices = &state.indices[state.current_index..batch_end];

        // Get dataset
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&state.dataset).cloned() else {
            return 0;
        };
        drop(dataset_registry);

        match dataset.as_ref() {
            DatasetState::TensorDataset { features, labels } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(feat_tensor) = tensor_registry.get(features).cloned() else {
                    return 0;
                };
                let Some(label_tensor) = tensor_registry.get(labels).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                // Gather batch samples using index_select
                let batch_indices_tensor = Tensor::from_slice(batch_indices).to_kind(tch::Kind::Int64);

                let batch_features = feat_tensor.0.index_select(0, &batch_indices_tensor);
                let batch_labels = label_tensor.0.index_select(0, &batch_indices_tensor);

                // Store in registry
                let feat_handle = super::super::next_handle();
                let label_handle = super::super::next_handle();

                TENSOR_REGISTRY
                    .lock()
                    .insert(feat_handle, Arc::new(TensorWrapper(batch_features)));
                TENSOR_REGISTRY
                    .lock()
                    .insert(label_handle, Arc::new(TensorWrapper(batch_labels)));

                // Advance index
                state.current_index = batch_end;

                tracing::debug!(
                    "rt_torch_dataloader_next: loader={} -> batch=({}, {})",
                    dataloader_handle,
                    feat_handle,
                    label_handle
                );

                feat_handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        0
    }
}

/// Reset dataloader to beginning for next epoch
/// Re-shuffles if shuffle was enabled
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_reset(dataloader_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let loader_registry = DATALOADER_REGISTRY.lock();
        let Some(loader) = loader_registry.get(&dataloader_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(loader_registry);

        let mut state = loader.lock();
        state.current_index = 0;

        // Re-shuffle if enabled
        if state.shuffle {
            use rand::seq::SliceRandom;
            let mut rng = rand::thread_rng();
            state.indices.shuffle(&mut rng);
        }

        tracing::debug!("rt_torch_dataloader_reset: loader={}", dataloader_handle);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Free a dataloader
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_free(dataloader_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut loader_registry = DATALOADER_REGISTRY.lock();
        if loader_registry.remove(&dataloader_handle).is_some() {
            tracing::debug!("rt_torch_dataloader_free: freed loader={}", dataloader_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        TorchFfiError::NotAvailable as i32
    }
}
