//! PyTorch Dataset implementations
//!
//! This module provides Dataset types for organizing training data,
//! supporting indexing and length queries.

#[cfg(feature = "pytorch")]
use tch::Tensor;

#[cfg(feature = "pytorch")]
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use super::super::{TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{next_dataset_handle, DATASET_REGISTRY};

use crate::value::torch::TorchFfiError;

// ============================================================================
// Dataset Types
// ============================================================================

/// Dataset types for data loading
#[cfg(feature = "pytorch")]
#[derive(Debug)]
pub enum DatasetState {
    /// TensorDataset: wraps feature and label tensors
    TensorDataset {
        features: u64, // Tensor handle [num_samples, ...]
        labels: u64,   // Tensor handle [num_samples, ...]
    },
}

// ============================================================================
// Dataset FFI Functions
// ============================================================================

/// Create a TensorDataset from feature and label tensors
/// features: tensor handle with shape [num_samples, ...]
/// labels: tensor handle with shape [num_samples]
#[no_mangle]
pub extern "C" fn rt_torch_tensor_dataset_new(features: u64, labels: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if features == 0 || labels == 0 {
            return 0;
        }

        // Verify tensors exist and get num_samples
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(feat_tensor) = tensor_registry.get(&features) else {
            return 0;
        };
        let Some(label_tensor) = tensor_registry.get(&labels) else {
            return 0;
        };

        // Check that both tensors have same first dimension (num_samples)
        let feat_shape = feat_tensor.0.size();
        let label_shape = label_tensor.0.size();

        if feat_shape.is_empty() || label_shape.is_empty() {
            return 0;
        }

        if feat_shape[0] != label_shape[0] {
            tracing::error!(
                "Feature and label tensors must have same num_samples: {} vs {}",
                feat_shape[0],
                label_shape[0]
            );
            return 0;
        }

        drop(tensor_registry);

        let dataset = DatasetState::TensorDataset { features, labels };
        let handle = next_dataset_handle();
        DATASET_REGISTRY.lock().insert(handle, Arc::new(dataset));

        tracing::debug!(
            "rt_torch_tensor_dataset_new: features={} labels={} -> dataset={}",
            features,
            labels,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (features, labels);
        0
    }
}

/// Get the length of a dataset (number of samples)
#[no_mangle]
pub extern "C" fn rt_torch_dataset_len(dataset_handle: u64) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&dataset_handle) else {
            return -1;
        };

        match dataset.as_ref() {
            DatasetState::TensorDataset { features, .. } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(feat_tensor) = tensor_registry.get(features) else {
                    return -1;
                };
                let shape = feat_tensor.0.size();
                if shape.is_empty() {
                    -1
                } else {
                    shape[0]
                }
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataset_handle;
        -1
    }
}

/// Get a single sample from the dataset
/// Returns a pointer to a struct containing (feature_tensor_handle, label_tensor_handle)
/// Caller must free the returned tensor handles
#[no_mangle]
pub extern "C" fn rt_torch_dataset_get(dataset_handle: u64, index: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&dataset_handle).cloned() else {
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

                // Get slice at index
                let feat_item = feat_tensor.0.get(index);
                let label_item = label_tensor.0.get(index);

                // Store in registry
                let feat_handle = super::super::next_handle();
                let label_handle = super::super::next_handle();

                TENSOR_REGISTRY
                    .lock()
                    .insert(feat_handle, Arc::new(TensorWrapper(feat_item)));
                TENSOR_REGISTRY
                    .lock()
                    .insert(label_handle, Arc::new(TensorWrapper(label_item)));

                // Return feature handle (label handle is feat_handle + 1)
                // Simplified: just return feature handle, caller must know to get label at +1
                feat_handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (dataset_handle, index);
        0
    }
}

/// Free a dataset
#[no_mangle]
pub extern "C" fn rt_torch_dataset_free(dataset_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut dataset_registry = DATASET_REGISTRY.lock();
        if let Some(dataset) = dataset_registry.remove(&dataset_handle) {
            // Free the tensors owned by the dataset
            match dataset.as_ref() {
                DatasetState::TensorDataset { features, labels } => {
                    super::super::rt_torch_free(*features);
                    super::super::rt_torch_free(*labels);
                }
            }

            tracing::debug!("rt_torch_dataset_free: freed dataset={}", dataset_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataset_handle;
        TorchFfiError::NotAvailable as i32
    }
}
