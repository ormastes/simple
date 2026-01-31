//! Broadcasting utilities for tensors.

use crate::error::CompileError;
use super::core::{Tensor, compute_strides};

/// Broadcast shapes for element-wise operations
pub fn broadcast_shapes(a: &[usize], b: &[usize]) -> Result<Vec<usize>, CompileError> {
    let max_len = a.len().max(b.len());
    let mut result = vec![0; max_len];

    for i in 0..max_len {
        let a_dim = if i < max_len - a.len() {
            1
        } else {
            a[i - (max_len - a.len())]
        };
        let b_dim = if i < max_len - b.len() {
            1
        } else {
            b[i - (max_len - b.len())]
        };

        if a_dim == b_dim {
            result[i] = a_dim;
        } else if a_dim == 1 {
            result[i] = b_dim;
        } else if b_dim == 1 {
            result[i] = a_dim;
        } else {
            return Err(crate::error::factory::tensor_cannot_broadcast_shapes(a, b));
        }
    }

    Ok(result)
}

/// Perform broadcast binary operation
pub(crate) fn broadcast_binary_op<F>(a: &Tensor, b: &Tensor, op: F) -> Result<Tensor, CompileError>
where
    F: Fn(f64, f64) -> f64,
{
    let result_shape = broadcast_shapes(&a.shape, &b.shape)?;
    let result_size: usize = result_shape.iter().product();
    let mut result_data = vec![0.0; result_size];

    // Compute strides for broadcasting
    let a_strides = compute_broadcast_strides(&a.shape, &result_shape);
    let b_strides = compute_broadcast_strides(&b.shape, &result_shape);
    let result_strides = compute_strides(&result_shape);

    // Iterate over result indices
    for flat_idx in 0..result_size {
        let mut remaining = flat_idx;
        let mut a_idx = 0;
        let mut b_idx = 0;

        for (i, &stride) in result_strides.iter().enumerate() {
            let coord = remaining / stride;
            remaining %= stride;
            a_idx += coord * a_strides[i];
            b_idx += coord * b_strides[i];
        }

        let a_val = if a.data.is_empty() {
            0.0
        } else {
            a.data[a_idx % a.data.len()]
        };
        let b_val = if b.data.is_empty() {
            0.0
        } else {
            b.data[b_idx % b.data.len()]
        };
        result_data[flat_idx] = op(a_val, b_val);
    }

    Tensor::new(result_data, result_shape)
}

/// Compute broadcast strides
fn compute_broadcast_strides(shape: &[usize], target_shape: &[usize]) -> Vec<usize> {
    let mut strides = vec![0; target_shape.len()];
    let offset = target_shape.len() - shape.len();
    let original_strides = compute_strides(shape);

    for (i, &dim) in shape.iter().enumerate() {
        if dim == target_shape[offset + i] {
            strides[offset + i] = original_strides[i];
        }
        // else stride remains 0 (broadcasting)
    }

    strides
}
