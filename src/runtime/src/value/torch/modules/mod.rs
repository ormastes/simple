//! Neural Network Modules
//!
//! This module provides high-level neural network building blocks including:
//! - Linear (fully connected) layers
//! - Convolutional layers (Conv2d) and pooling
//! - Normalization layers (BatchNorm2d, LayerNorm)
//! - Regularization (Dropout)
//! - Embedding layers
//! - Recurrent layers (LSTM, GRU)

#[cfg(feature = "pytorch")]
use parking_lot::Mutex;

#[cfg(feature = "pytorch")]
use std::collections::HashMap;

#[cfg(feature = "pytorch")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

// Re-export items that submodules need
#[cfg(feature = "pytorch")]
pub(super) use super::registry::{TENSOR_REGISTRY, TensorWrapper, next_handle};

#[cfg(feature = "pytorch")]
pub(super) use super::creation::{rt_torch_randn, rt_torch_zeros, rt_torch_ones, rt_torch_free};

#[cfg(feature = "pytorch")]
pub(super) use super::autograd::{rt_torch_set_requires_grad, rt_torch_detach};

#[cfg(feature = "pytorch")]
pub(super) use super::nn_initialization::rt_torch_kaiming_uniform_;

#[cfg(feature = "pytorch")]
pub(super) use super::ops_matrix::{rt_torch_transpose, rt_torch_matmul};

#[cfg(feature = "pytorch")]
pub(super) use super::ops_elementwise::rt_torch_add;

#[cfg(feature = "pytorch")]
pub(super) use super::ops_shape::rt_torch_clone;

pub mod linear;
pub mod conv;
pub mod batchnorm;
pub mod dropout;
pub mod layernorm;
pub mod embedding;
pub mod rnn;

// Re-export module functions
pub use linear::*;
pub use conv::*;
pub use batchnorm::*;
pub use dropout::*;
pub use layernorm::*;
pub use embedding::*;
pub use rnn::*;

/// Module state enum for different layer types
#[cfg(feature = "pytorch")]
#[derive(Debug)]
pub(crate) enum ModuleState {
    Linear {
        weight: u64,  // Tensor handle
        bias: Option<u64>,  // Optional bias tensor handle
    },
    Conv2d {
        weight: u64,
        bias: Option<u64>,
        stride: (i64, i64),
        padding: (i64, i64),
    },
    BatchNorm2d {
        weight: u64,  // Scale (gamma)
        bias: u64,    // Shift (beta)
        running_mean: u64,
        running_var: u64,
        eps: f64,
        momentum: f64,
        num_batches_tracked: usize,
    },
    LSTM {
        input_size: i64,
        hidden_size: i64,
        num_layers: i64,
        bidirectional: bool,
        // Weights stored as tensor handles per layer
        // Format: [(weight_ih, weight_hh, bias_ih, bias_hh), ...] for each layer
        weights: Vec<(u64, u64, u64, u64)>,
    },
    GRU {
        input_size: i64,
        hidden_size: i64,
        num_layers: i64,
        bidirectional: bool,
        // Weights per layer: (weight_ih, weight_hh, bias_ih, bias_hh)
        weights: Vec<(u64, u64, u64, u64)>,
    },
    Dropout {
        p: f64,       // Dropout probability
        inplace: bool, // Whether to modify input in-place
    },
    LayerNorm {
        normalized_shape: Vec<i64>,  // Shape to normalize over
        weight: u64,   // Scale (gamma) parameter
        bias: u64,     // Shift (beta) parameter
        eps: f64,      // Epsilon for numerical stability
    },
    Embedding {
        num_embeddings: i64,  // Vocabulary size
        embedding_dim: i64,   // Embedding dimension
        weight: u64,          // Embedding weight matrix [num_embeddings, embedding_dim]
        padding_idx: Option<i64>,  // Optional padding index
    },
}

/// Global module registry
#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    pub(crate) static ref MODULE_REGISTRY: Mutex<HashMap<u64, Arc<ModuleState>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_MODULE_HANDLE: AtomicU64 = AtomicU64::new(1);
}

/// Get next module handle
#[cfg(feature = "pytorch")]
pub(crate) fn next_module_handle() -> u64 {
    NEXT_MODULE_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Free a module and its parameters
#[no_mangle]
pub extern "C" fn rt_torch_module_free(module_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        use super::error::TorchFfiError;

        let mut module_registry = MODULE_REGISTRY.lock();
        if let Some(module) = module_registry.remove(&module_handle) {
            // Free the tensors owned by the module
            match module.as_ref() {
                ModuleState::Linear { weight, bias } => {
                    rt_torch_free(*weight);
                    if let Some(b) = bias {
                        rt_torch_free(*b);
                    }
                }
                ModuleState::Conv2d { weight, bias, .. } => {
                    rt_torch_free(*weight);
                    if let Some(b) = bias {
                        rt_torch_free(*b);
                    }
                }
                ModuleState::BatchNorm2d {
                    weight,
                    bias,
                    running_mean,
                    running_var,
                    ..
                } => {
                    rt_torch_free(*weight);
                    rt_torch_free(*bias);
                    rt_torch_free(*running_mean);
                    rt_torch_free(*running_var);
                }
                ModuleState::LSTM { weights, .. } | ModuleState::GRU { weights, .. } => {
                    // Free all weight tensors for each layer
                    for (weight_ih, weight_hh, bias_ih, bias_hh) in weights {
                        rt_torch_free(*weight_ih);
                        rt_torch_free(*weight_hh);
                        rt_torch_free(*bias_ih);
                        rt_torch_free(*bias_hh);
                    }
                }
                ModuleState::Dropout { .. } => {
                    // Dropout has no tensor handles to free
                }
                ModuleState::LayerNorm { weight, bias, .. } => {
                    rt_torch_free(*weight);
                    rt_torch_free(*bias);
                }
                ModuleState::Embedding { weight, .. } => {
                    rt_torch_free(*weight);
                }
            }

            tracing::debug!("rt_torch_module_free: freed module={}", module_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        use super::error::TorchFfiError;
        let _ = module_handle;
        TorchFfiError::NotAvailable as i32
    }
}
