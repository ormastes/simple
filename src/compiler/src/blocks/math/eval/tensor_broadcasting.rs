//! Tensor broadcasting and conversion utilities.
//!
//! Provides NumPy-style broadcasting for tensor operations and
//! conversion between nested Value arrays and flat Tensor representation.

use super::super::tensor::Tensor;
use super::MathValue;
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

/// Convert tensor to nested Value::Array
pub fn tensor_to_value(tensor: &Tensor) -> Value {
    if tensor.shape.is_empty() {
        // Scalar tensor
        return Value::Float(tensor.data[0]);
    }

    if tensor.shape.len() == 1 {
        // 1D tensor -> simple array
        return Value::Array(tensor.data.iter().map(|&x| Value::Float(x)).collect());
    }

    // Multi-dimensional: build nested arrays
    fn build_nested(data: &[f64], shape: &[usize], offset: usize) -> Value {
        if shape.len() == 1 {
            Value::Array(
                data[offset..offset + shape[0]]
                    .iter()
                    .map(|&x| Value::Float(x))
                    .collect(),
            )
        } else {
            let inner_size: usize = shape[1..].iter().product();
            Value::Array(
                (0..shape[0])
                    .map(|i| build_nested(data, &shape[1..], offset + i * inner_size))
                    .collect(),
            )
        }
    }

    build_nested(&tensor.data, &tensor.shape, 0)
}

/// Flatten nested MathValues to tensor data and shape
pub fn flatten_to_tensor(values: &[MathValue]) -> Result<(Vec<f64>, Vec<usize>), CompileError> {
    if values.is_empty() {
        return Ok((vec![], vec![0]));
    }

    // Check first element to determine structure
    match &values[0] {
        MathValue::Int(_) | MathValue::Float(_) | MathValue::Bool(_) => {
            // All elements should be scalars
            let data: Vec<f64> = values.iter().map(|v| v.as_f64()).collect::<Result<_, _>>()?;
            Ok((data, vec![values.len()]))
        }
        MathValue::Tensor(t) => {
            // All elements should be tensors of same shape
            let inner_shape = t.shape.clone();
            let mut data = Vec::new();

            for v in values {
                match v {
                    MathValue::Tensor(t2) => {
                        if t2.shape != inner_shape {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help("all nested tensors must have the same shape");
                            return Err(CompileError::semantic_with_context(
                                "inconsistent shapes in nested array".to_string(),
                                ctx,
                            ));
                        }
                        data.extend(&t2.data);
                    }
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("cannot mix scalar values and tensors in the same array");
                        return Err(CompileError::semantic_with_context("mixed scalar and tensor in array".to_string(), ctx));
                    }
                }
            }

            let mut shape = vec![values.len()];
            shape.extend(inner_shape);
            Ok((data, shape))
        }
    }
}

/// Broadcast tensor operation with NumPy-style broadcasting
pub fn broadcast_tensor_op<F>(a: &Tensor, b: &Tensor, op: F) -> Result<Tensor, CompileError>
where
    F: Fn(f64, f64) -> f64,
{
    // Simple case: same shape
    if a.shape == b.shape {
        let data: Vec<f64> = a.data.iter().zip(b.data.iter()).map(|(&x, &y)| op(x, y)).collect();
        return Tensor::new(data, a.shape.clone());
    }

    // Use tensor's broadcasting
    let scalar_a = Tensor::new(a.data.clone(), a.shape.clone())?;
    let scalar_b = Tensor::new(b.data.clone(), b.shape.clone())?;

    // Manual broadcast
    let result_shape = broadcast_shapes(&a.shape, &b.shape)?;
    let result_size: usize = result_shape.iter().product();
    let mut result_data = vec![0.0; result_size];

    for i in 0..result_size {
        let a_idx = broadcast_index(i, &result_shape, &a.shape);
        let b_idx = broadcast_index(i, &result_shape, &b.shape);
        result_data[i] = op(scalar_a.data[a_idx], scalar_b.data[b_idx]);
    }

    Tensor::new(result_data, result_shape)
}

/// Compute broadcast shapes using NumPy broadcasting rules
///
/// NumPy broadcasting rules:
/// - Dimensions are aligned from the right (trailing dimensions)
/// - Each dimension must be either equal or one of them must be 1
/// - Result shape is the maximum of each aligned dimension
///
/// Examples:
/// - (3, 1) + (3, 4) → (3, 4)
/// - (5, 1, 4) + (3, 4) → (5, 3, 4)
/// - (2, 3) + (2, 3) → (2, 3)
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

/// Compute index in source array for broadcast
///
/// Maps a flat index in the result tensor to the corresponding
/// flat index in the source tensor, handling dimension broadcasting.
///
/// When a dimension is size 1 in the source, the index is clamped to 0
/// (repeating that element across the broadcast dimension).
pub fn broadcast_index(flat_idx: usize, result_shape: &[usize], source_shape: &[usize]) -> usize {
    let offset = result_shape.len() - source_shape.len();
    let mut source_idx = 0;
    let mut remaining = flat_idx;

    let result_strides: Vec<usize> = {
        let mut s = vec![1; result_shape.len()];
        for i in (0..result_shape.len() - 1).rev() {
            s[i] = s[i + 1] * result_shape[i + 1];
        }
        s
    };

    let source_strides: Vec<usize> = {
        let mut s = vec![1; source_shape.len()];
        for i in (0..source_shape.len() - 1).rev() {
            s[i] = s[i + 1] * source_shape[i + 1];
        }
        s
    };

    for (i, &stride) in result_strides.iter().enumerate() {
        let coord = remaining / stride;
        remaining %= stride;

        if i >= offset {
            let src_i = i - offset;
            let src_coord = if source_shape[src_i] == 1 { 0 } else { coord };
            source_idx += src_coord * source_strides[src_i];
        }
    }

    source_idx
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_broadcast_shapes_same() {
        let result = broadcast_shapes(&[2, 3], &[2, 3]).unwrap();
        assert_eq!(result, vec![2, 3]);
    }

    #[test]
    fn test_broadcast_shapes_scalar() {
        let result = broadcast_shapes(&[1], &[3, 4]).unwrap();
        assert_eq!(result, vec![3, 4]);
    }

    #[test]
    fn test_broadcast_shapes_trailing_one() {
        let result = broadcast_shapes(&[3, 1], &[3, 4]).unwrap();
        assert_eq!(result, vec![3, 4]);
    }

    #[test]
    fn test_broadcast_shapes_different_ndim() {
        let result = broadcast_shapes(&[5, 1, 4], &[3, 4]).unwrap();
        assert_eq!(result, vec![5, 3, 4]);
    }

    #[test]
    fn test_broadcast_shapes_incompatible() {
        let result = broadcast_shapes(&[2, 3], &[2, 4]);
        assert!(result.is_err());
    }

    #[test]
    fn test_flatten_scalars() {
        let values = vec![MathValue::Int(1), MathValue::Int(2), MathValue::Int(3)];
        let (data, shape) = flatten_to_tensor(&values).unwrap();
        assert_eq!(data, vec![1.0, 2.0, 3.0]);
        assert_eq!(shape, vec![3]);
    }

    #[test]
    fn test_tensor_to_value_scalar() {
        let tensor = Tensor::scalar(42.0);
        let value = tensor_to_value(&tensor);
        assert_eq!(value, Value::Float(42.0));
    }

    #[test]
    fn test_tensor_to_value_1d() {
        let tensor = Tensor::new(vec![1.0, 2.0, 3.0], vec![3]).unwrap();
        let value = tensor_to_value(&tensor);
        match value {
            Value::Array(arr) => {
                assert_eq!(arr.len(), 3);
                assert_eq!(arr[0], Value::Float(1.0));
            }
            _ => panic!("expected array"),
        }
    }
}
