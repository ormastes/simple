//! PyTorch/ML Integration FFI functions for Simple runtime.
//!
//! This module provides comprehensive PyTorch and machine learning operations,
//! organized into focused submodules for better maintainability.
//!
//! **Note:** This module requires the `pytorch` feature to be enabled:
//! ```toml
//! simple-runtime = { features = ["pytorch"] }
//! ```
//!
//! ## Module Organization
//!
//! - **storage**: Tensor storage and handle management (with atomic counters)
//! - **tensor_ops**: Basic tensor operations (arithmetic, indexing, slicing, stacking)
//! - **autograd**: Autograd context, gradients, and checkpointing
//! - **losses**: Loss functions (BCE, cross-entropy)
//! - **layers**: Neural network layers (Conv3D, RNN, Attention, Transformer)
//! - **optimizers**: Optimization algorithms (RMSProp, etc.)
//! - **serialization**: JIT compilation and model save/load
//! - **onnx**: ONNX export/import
//! - **datasets**: Dataset loaders (MNIST, CIFAR-10)
//! - **distributed**: Distributed training (DDP, collectives)

// Submodules
pub mod storage;
pub mod tensor_ops;
pub mod autograd;
pub mod losses;
pub mod layers;
pub mod optimizers;
pub mod serialization;
pub mod onnx;
pub mod datasets;
pub mod distributed;

// Re-export storage items for convenience
#[cfg(feature = "pytorch")]
pub use storage::{
    get_autograd_ctx, get_autograd_ctx_mut, get_tensor, get_tensor_list, remove_tensor,
    store_autograd_ctx, store_tensor, store_tensor_list, value_to_tensor_handle, AutogradContext,
};

// Re-export tensor operations
pub use tensor_ops::*;

// Re-export autograd operations
pub use autograd::*;

// Re-export loss functions
pub use losses::*;

// Re-export layer operations
pub use layers::*;

// Re-export optimizer operations
pub use optimizers::*;

// Re-export serialization operations
pub use serialization::*;

// Re-export ONNX operations
pub use onnx::*;

// Re-export dataset operations
pub use datasets::*;

// Re-export distributed operations
pub use distributed::*;
