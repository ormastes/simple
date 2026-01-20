//! Tensor operations for math blocks.
//!
//! Provides torch-compatible tensor operations:
//! - Creation: tensor(), zeros(), ones(), randn(), arange(), linspace()
//! - Element-wise: add, sub, mul, div, pow, neg, abs, sqrt, exp, log
//! - Reduction: sum, mean, prod, min, max, argmin, argmax
//! - Matrix ops: matmul, dot, transpose, reshape
//! - Indexing: slicing, advanced indexing

mod broadcast;
mod core;
mod creation;
mod elementwise;
mod indexing;
mod matrix;
mod reduction;

#[cfg(test)]
mod tests;

// Re-export the Tensor struct for backward compatibility
pub use core::Tensor;

// Re-export broadcast utilities
pub use broadcast::broadcast_shapes;
