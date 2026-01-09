//! PyTorch tensor FFI bridge
//!
//! This module provides FFI functions for PyTorch tensor operations,
//! following the handle-based registry pattern.
//!
//! Key patterns:
//! - Handle-based resource management (u64 handles → Arc<Tensor>)
//! - Global registries with Mutex for thread-safety
//! - Feature-gated compilation (#[cfg(feature = "pytorch")])
//! - Error codes: 0 = failure, positive = success/handle
//! - RAII cleanup via Arc reference counting
//!
//! # Module Organization
//!
//! - `error` - Error codes and types
//! - `registry` - Handle registry and helper functions
//! - `creation` - Tensor creation and availability functions
//! - `metadata` - Shape, dtype, device queries
//! - `ops_elementwise` - Element-wise operations (add, mul, etc.)
//! - `ops_matrix` - Matrix operations (matmul, transpose, etc.)
//! - `ops_shape` - Shape manipulation (reshape, permute, etc.)
//! - `ops_reduction` - Reduction operations (sum, mean, max, etc.)
//! - `ops_comparison` - Comparison operations (eq, gt, etc.)
//! - `device` - Device movement operations
//! - `data_access` - Data copying and item extraction
//! - `autograd` - Automatic differentiation
//! - `nn_activations` - Activation functions
//! - `nn_loss` - Loss functions
//! - `nn_normalization` - Normalization and dropout
//! - `nn_initialization` - Weight initialization
//! - `optimizer` - Optimizers (SGD, Adam, AdamW)
//! - `modules` - Neural network modules (Linear, Conv2d, etc.)
//! - `scheduler` - Learning rate schedulers
//! - `data` - Dataset and DataLoader
//! - `linalg` - Linear algebra operations (Simple Math #1950-#1959)
//! - `fft` - Fast Fourier Transform operations (Simple Math #1950-#1959)

// Public modules
mod autograd;
mod creation;
pub mod data;
mod data_access;
mod device;
pub mod error;
mod fft;
mod linalg;
mod metadata;
pub mod modules;
mod nn_activations;
mod nn_initialization;
mod nn_loss;
mod nn_normalization;
mod ops_comparison;
mod ops_elementwise;
mod ops_matrix;
mod ops_reduction;
mod ops_shape;
mod optimizer;
mod registry;
mod scheduler;

// Re-export error types
pub use error::TorchFfiError;

// Re-export all FFI functions from submodules
pub use autograd::*;
pub use creation::*;
pub use data::*;
pub use data_access::*;
pub use device::*;
pub use fft::*;
pub use linalg::*;
pub use metadata::*;
pub use modules::*;
pub use nn_activations::*;
pub use nn_initialization::*;
pub use nn_loss::*;
pub use nn_normalization::*;
pub use ops_comparison::*;
pub use ops_elementwise::*;
pub use ops_matrix::*;
pub use ops_reduction::*;
pub use ops_shape::*;
pub use optimizer::*;
pub use scheduler::*;
