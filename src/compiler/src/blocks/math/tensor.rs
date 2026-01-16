//! Tensor operations for math blocks.
//!
//! Provides torch-compatible tensor operations:
//! - Creation: tensor(), zeros(), ones(), randn(), arange(), linspace()
//! - Element-wise: add, sub, mul, div, pow, neg, abs, sqrt, exp, log
//! - Reduction: sum, mean, prod, min, max, argmin, argmax
//! - Matrix ops: matmul, dot, transpose, reshape
//! - Indexing: slicing, advanced indexing

use crate::error::CompileError;
use std::fmt;

/// N-dimensional tensor with f64 elements
#[derive(Clone, PartialEq)]
pub struct Tensor {
    /// Flattened data in row-major order
    pub data: Vec<f64>,
    /// Shape of the tensor
    pub shape: Vec<usize>,
    /// Strides for each dimension
    pub strides: Vec<usize>,
}

impl fmt::Debug for Tensor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tensor(shape={:?}, data={:?})", self.shape, self.data)
    }
}

impl Tensor {
    // ==========================================================================
    // Creation functions
    // ==========================================================================

    /// Create tensor from flat data and shape
    pub fn new(data: Vec<f64>, shape: Vec<usize>) -> Result<Self, CompileError> {
        let expected_len: usize = shape.iter().product();
        if data.len() != expected_len {
            return Err(CompileError::Semantic(format!(
                "tensor data length {} doesn't match shape {:?} (expected {})",
                data.len(),
                shape,
                expected_len
            )));
        }
        let strides = compute_strides(&shape);
        Ok(Self { data, shape, strides })
    }

    /// Create tensor from nested arrays (Python-style)
    pub fn from_nested(values: &[f64], shape: Vec<usize>) -> Result<Self, CompileError> {
        Self::new(values.to_vec(), shape)
    }

    /// Create scalar tensor (0-dimensional)
    pub fn scalar(value: f64) -> Self {
        Self {
            data: vec![value],
            shape: vec![],
            strides: vec![],
        }
    }

    /// Create tensor filled with zeros
    pub fn zeros(shape: Vec<usize>) -> Self {
        let size: usize = shape.iter().product();
        let strides = compute_strides(&shape);
        Self {
            data: vec![0.0; size],
            shape,
            strides,
        }
    }

    /// Create tensor filled with ones
    pub fn ones(shape: Vec<usize>) -> Self {
        let size: usize = shape.iter().product();
        let strides = compute_strides(&shape);
        Self {
            data: vec![1.0; size],
            shape,
            strides,
        }
    }

    /// Create tensor filled with a constant value
    pub fn full(shape: Vec<usize>, value: f64) -> Self {
        let size: usize = shape.iter().product();
        let strides = compute_strides(&shape);
        Self {
            data: vec![value; size],
            shape,
            strides,
        }
    }

    /// Create identity matrix
    pub fn eye(n: usize) -> Self {
        let mut data = vec![0.0; n * n];
        for i in 0..n {
            data[i * n + i] = 1.0;
        }
        Self {
            data,
            shape: vec![n, n],
            strides: vec![n, 1],
        }
    }

    /// Create range tensor: arange(start, end, step)
    pub fn arange(start: f64, end: f64, step: f64) -> Self {
        let mut data = Vec::new();
        let mut x = start;
        while (step > 0.0 && x < end) || (step < 0.0 && x > end) {
            data.push(x);
            x += step;
        }
        let len = data.len();
        Self {
            data,
            shape: vec![len],
            strides: vec![1],
        }
    }

    /// Create linearly spaced tensor
    pub fn linspace(start: f64, end: f64, steps: usize) -> Self {
        if steps == 0 {
            return Self::zeros(vec![0]);
        }
        if steps == 1 {
            return Self {
                data: vec![start],
                shape: vec![1],
                strides: vec![1],
            };
        }
        let step = (end - start) / (steps - 1) as f64;
        let data: Vec<f64> = (0..steps).map(|i| start + i as f64 * step).collect();
        Self {
            data,
            shape: vec![steps],
            strides: vec![1],
        }
    }

    /// Create random tensor with uniform distribution [0, 1)
    pub fn rand(shape: Vec<usize>) -> Self {
        let size: usize = shape.iter().product();
        // Simple LCG random number generator for reproducibility
        let mut seed: u64 = 12345;
        let data: Vec<f64> = (0..size)
            .map(|_| {
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
                seed as f64 / u64::MAX as f64
            })
            .collect();
        let strides = compute_strides(&shape);
        Self { data, shape, strides }
    }

    /// Create random tensor with standard normal distribution
    pub fn randn(shape: Vec<usize>) -> Self {
        let size: usize = shape.iter().product();
        let mut seed: u64 = 54321;
        // Box-Muller transform for normal distribution
        let data: Vec<f64> = (0..size)
            .map(|_| {
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
                let u1 = (seed as f64 / u64::MAX as f64).max(1e-10);
                seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
                let u2 = seed as f64 / u64::MAX as f64;
                (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
            })
            .collect();
        let strides = compute_strides(&shape);
        Self { data, shape, strides }
    }

    // ==========================================================================
    // Properties
    // ==========================================================================

    /// Number of dimensions
    pub fn ndim(&self) -> usize {
        self.shape.len()
    }

    /// Total number of elements
    pub fn numel(&self) -> usize {
        self.data.len()
    }

    /// Check if tensor is scalar (0-dimensional)
    pub fn is_scalar(&self) -> bool {
        self.shape.is_empty()
    }

    /// Get scalar value (panics if not scalar)
    pub fn item(&self) -> Result<f64, CompileError> {
        if self.data.len() != 1 {
            return Err(CompileError::Semantic(format!(
                "item() requires exactly one element, tensor has {}",
                self.data.len()
            )));
        }
        Ok(self.data[0])
    }

    // ==========================================================================
    // Element-wise operations
    // ==========================================================================

    /// Element-wise addition with broadcasting
    pub fn add(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        broadcast_binary_op(self, other, |a, b| a + b)
    }

    /// Element-wise subtraction with broadcasting
    pub fn sub(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        broadcast_binary_op(self, other, |a, b| a - b)
    }

    /// Element-wise multiplication with broadcasting
    pub fn mul(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        broadcast_binary_op(self, other, |a, b| a * b)
    }

    /// Element-wise division with broadcasting
    pub fn div(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        broadcast_binary_op(self, other, |a, b| {
            if b == 0.0 {
                f64::NAN
            } else {
                a / b
            }
        })
    }

    /// Element-wise power
    pub fn pow(&self, exp: &Tensor) -> Result<Tensor, CompileError> {
        broadcast_binary_op(self, exp, |a, b| a.powf(b))
    }

    /// Element-wise negation
    pub fn neg(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| -x).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise absolute value
    pub fn abs(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.abs()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise square root
    pub fn sqrt(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.sqrt()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise exponential
    pub fn exp(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.exp()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise natural logarithm
    pub fn log(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.ln()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise sine
    pub fn sin(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.sin()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise cosine
    pub fn cos(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.cos()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise tangent
    pub fn tan(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.tan()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise hyperbolic tangent (common in ML)
    pub fn tanh(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.tanh()).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise sigmoid function
    pub fn sigmoid(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| 1.0 / (1.0 + (-x).exp())).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    /// Element-wise ReLU
    pub fn relu(&self) -> Tensor {
        Self {
            data: self.data.iter().map(|x| x.max(0.0)).collect(),
            shape: self.shape.clone(),
            strides: self.strides.clone(),
        }
    }

    // ==========================================================================
    // Reduction operations
    // ==========================================================================

    /// Sum all elements
    pub fn sum(&self) -> f64 {
        self.data.iter().sum()
    }

    /// Sum along axis
    pub fn sum_axis(&self, axis: usize) -> Result<Tensor, CompileError> {
        reduce_axis(self, axis, |slice| slice.iter().sum())
    }

    /// Mean of all elements
    pub fn mean(&self) -> f64 {
        if self.data.is_empty() {
            return f64::NAN;
        }
        self.sum() / self.data.len() as f64
    }

    /// Mean along axis
    pub fn mean_axis(&self, axis: usize) -> Result<Tensor, CompileError> {
        let n = self.shape.get(axis).copied().unwrap_or(1) as f64;
        reduce_axis(self, axis, |slice| slice.iter().sum::<f64>() / n)
    }

    /// Product of all elements
    pub fn prod(&self) -> f64 {
        self.data.iter().product()
    }

    /// Minimum element
    pub fn min(&self) -> f64 {
        self.data.iter().cloned().fold(f64::INFINITY, f64::min)
    }

    /// Maximum element
    pub fn max(&self) -> f64 {
        self.data.iter().cloned().fold(f64::NEG_INFINITY, f64::max)
    }

    /// Index of minimum element
    pub fn argmin(&self) -> usize {
        self.data
            .iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
            .map(|(i, _)| i)
            .unwrap_or(0)
    }

    /// Index of maximum element
    pub fn argmax(&self) -> usize {
        self.data
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
            .map(|(i, _)| i)
            .unwrap_or(0)
    }

    /// Variance of all elements
    pub fn var(&self) -> f64 {
        let mean = self.mean();
        let n = self.data.len() as f64;
        if n == 0.0 {
            return f64::NAN;
        }
        self.data.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / n
    }

    /// Standard deviation
    pub fn std(&self) -> f64 {
        self.var().sqrt()
    }

    // ==========================================================================
    // Matrix operations
    // ==========================================================================

    /// Matrix multiplication (2D tensors)
    pub fn matmul(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        if self.ndim() != 2 || other.ndim() != 2 {
            return Err(CompileError::Semantic(
                "matmul requires 2D tensors".to_string(),
            ));
        }

        let (m, k1) = (self.shape[0], self.shape[1]);
        let (k2, n) = (other.shape[0], other.shape[1]);

        if k1 != k2 {
            return Err(CompileError::Semantic(format!(
                "matmul shape mismatch: ({}, {}) @ ({}, {})",
                m, k1, k2, n
            )));
        }

        let mut result = vec![0.0; m * n];
        for i in 0..m {
            for j in 0..n {
                let mut sum = 0.0;
                for k in 0..k1 {
                    sum += self.data[i * k1 + k] * other.data[k * n + j];
                }
                result[i * n + j] = sum;
            }
        }

        Tensor::new(result, vec![m, n])
    }

    /// Dot product of 1D tensors
    pub fn dot(&self, other: &Tensor) -> Result<f64, CompileError> {
        if self.ndim() != 1 || other.ndim() != 1 {
            return Err(CompileError::Semantic("dot requires 1D tensors".to_string()));
        }
        if self.shape[0] != other.shape[0] {
            return Err(CompileError::Semantic(format!(
                "dot shape mismatch: {} vs {}",
                self.shape[0], other.shape[0]
            )));
        }
        Ok(self
            .data
            .iter()
            .zip(other.data.iter())
            .map(|(a, b)| a * b)
            .sum())
    }

    /// Transpose (swap last two dimensions)
    pub fn transpose(&self) -> Result<Tensor, CompileError> {
        if self.ndim() < 2 {
            return Err(CompileError::Semantic(
                "transpose requires at least 2D tensor".to_string(),
            ));
        }

        let n = self.ndim();
        let (rows, cols) = (self.shape[n - 2], self.shape[n - 1]);

        // For 2D, simple transpose
        if n == 2 {
            let mut data = vec![0.0; rows * cols];
            for i in 0..rows {
                for j in 0..cols {
                    data[j * rows + i] = self.data[i * cols + j];
                }
            }
            return Tensor::new(data, vec![cols, rows]);
        }

        // For higher dims, transpose last two dimensions
        let batch_size: usize = self.shape[..n - 2].iter().product();
        let matrix_size = rows * cols;
        let mut data = vec![0.0; self.data.len()];

        for b in 0..batch_size {
            let offset = b * matrix_size;
            for i in 0..rows {
                for j in 0..cols {
                    data[offset + j * rows + i] = self.data[offset + i * cols + j];
                }
            }
        }

        let mut new_shape = self.shape.clone();
        new_shape[n - 2] = cols;
        new_shape[n - 1] = rows;
        Tensor::new(data, new_shape)
    }

    /// Reshape tensor to new shape
    pub fn reshape(&self, new_shape: Vec<usize>) -> Result<Tensor, CompileError> {
        let new_size: usize = new_shape.iter().product();
        if new_size != self.data.len() {
            return Err(CompileError::Semantic(format!(
                "cannot reshape tensor of size {} to {:?}",
                self.data.len(),
                new_shape
            )));
        }
        Tensor::new(self.data.clone(), new_shape)
    }

    /// Flatten to 1D
    pub fn flatten(&self) -> Tensor {
        Tensor {
            data: self.data.clone(),
            shape: vec![self.data.len()],
            strides: vec![1],
        }
    }

    /// Squeeze: remove dimensions of size 1
    pub fn squeeze(&self) -> Tensor {
        let new_shape: Vec<usize> = self.shape.iter().copied().filter(|&s| s != 1).collect();
        let strides = compute_strides(&new_shape);
        Tensor {
            data: self.data.clone(),
            shape: if new_shape.is_empty() {
                vec![]
            } else {
                new_shape
            },
            strides,
        }
    }

    /// Unsqueeze: add dimension of size 1 at position
    pub fn unsqueeze(&self, dim: usize) -> Result<Tensor, CompileError> {
        if dim > self.shape.len() {
            return Err(CompileError::Semantic(format!(
                "unsqueeze dim {} out of range for tensor with {} dims",
                dim,
                self.shape.len()
            )));
        }
        let mut new_shape = self.shape.clone();
        new_shape.insert(dim, 1);
        Tensor::new(self.data.clone(), new_shape)
    }

    // ==========================================================================
    // Indexing
    // ==========================================================================

    /// Get element at index
    pub fn get(&self, indices: &[usize]) -> Result<f64, CompileError> {
        if indices.len() != self.shape.len() {
            return Err(CompileError::Semantic(format!(
                "expected {} indices, got {}",
                self.shape.len(),
                indices.len()
            )));
        }
        let mut flat_idx = 0;
        for (i, &idx) in indices.iter().enumerate() {
            if idx >= self.shape[i] {
                return Err(CompileError::Semantic(format!(
                    "index {} out of bounds for dimension {} with size {}",
                    idx, i, self.shape[i]
                )));
            }
            flat_idx += idx * self.strides[i];
        }
        Ok(self.data[flat_idx])
    }

    /// Set element at index
    pub fn set(&mut self, indices: &[usize], value: f64) -> Result<(), CompileError> {
        if indices.len() != self.shape.len() {
            return Err(CompileError::Semantic(format!(
                "expected {} indices, got {}",
                self.shape.len(),
                indices.len()
            )));
        }
        let mut flat_idx = 0;
        for (i, &idx) in indices.iter().enumerate() {
            if idx >= self.shape[i] {
                return Err(CompileError::Semantic(format!(
                    "index {} out of bounds for dimension {} with size {}",
                    idx, i, self.shape[i]
                )));
            }
            flat_idx += idx * self.strides[i];
        }
        self.data[flat_idx] = value;
        Ok(())
    }
}

// ==========================================================================
// Helper functions
// ==========================================================================

/// Compute strides for row-major layout
fn compute_strides(shape: &[usize]) -> Vec<usize> {
    if shape.is_empty() {
        return vec![];
    }
    let mut strides = vec![1; shape.len()];
    for i in (0..shape.len() - 1).rev() {
        strides[i] = strides[i + 1] * shape[i + 1];
    }
    strides
}

/// Broadcast shapes for element-wise operations
fn broadcast_shapes(a: &[usize], b: &[usize]) -> Result<Vec<usize>, CompileError> {
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
            return Err(CompileError::Semantic(format!(
                "cannot broadcast shapes {:?} and {:?}",
                a, b
            )));
        }
    }

    Ok(result)
}

/// Perform broadcast binary operation
fn broadcast_binary_op<F>(a: &Tensor, b: &Tensor, op: F) -> Result<Tensor, CompileError>
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

        let a_val = if a.data.is_empty() { 0.0 } else { a.data[a_idx % a.data.len()] };
        let b_val = if b.data.is_empty() { 0.0 } else { b.data[b_idx % b.data.len()] };
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

/// Reduce along axis
fn reduce_axis<F>(tensor: &Tensor, axis: usize, reducer: F) -> Result<Tensor, CompileError>
where
    F: Fn(&[f64]) -> f64,
{
    if axis >= tensor.ndim() {
        return Err(CompileError::Semantic(format!(
            "axis {} out of bounds for tensor with {} dimensions",
            axis,
            tensor.ndim()
        )));
    }

    let axis_size = tensor.shape[axis];
    let mut result_shape = tensor.shape.clone();
    result_shape.remove(axis);

    if result_shape.is_empty() {
        // Result is scalar
        return Ok(Tensor::scalar(reducer(&tensor.data)));
    }

    let result_size: usize = result_shape.iter().product();
    let mut result_data = Vec::with_capacity(result_size);

    // Pre-compute strides
    let outer_size: usize = tensor.shape[..axis].iter().product();
    let inner_size: usize = tensor.shape[axis + 1..].iter().product();

    for outer in 0..outer_size {
        for inner in 0..inner_size {
            let mut slice = Vec::with_capacity(axis_size);
            for i in 0..axis_size {
                let idx = outer * axis_size * inner_size + i * inner_size + inner;
                slice.push(tensor.data[idx]);
            }
            result_data.push(reducer(&slice));
        }
    }

    Tensor::new(result_data, result_shape)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tensor_creation() {
        let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        assert_eq!(t.shape, vec![2, 2]);
        assert_eq!(t.data, vec![1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_zeros() {
        let t = Tensor::zeros(vec![2, 3]);
        assert_eq!(t.shape, vec![2, 3]);
        assert_eq!(t.data, vec![0.0; 6]);
    }

    #[test]
    fn test_ones() {
        let t = Tensor::ones(vec![2, 2]);
        assert_eq!(t.data, vec![1.0; 4]);
    }

    #[test]
    fn test_eye() {
        let t = Tensor::eye(3);
        assert_eq!(t.shape, vec![3, 3]);
        assert_eq!(t.data, vec![1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0]);
    }

    #[test]
    fn test_arange() {
        let t = Tensor::arange(0.0, 5.0, 1.0);
        assert_eq!(t.data, vec![0.0, 1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn test_linspace() {
        let t = Tensor::linspace(0.0, 1.0, 5);
        assert_eq!(t.shape, vec![5]);
        assert!((t.data[0] - 0.0).abs() < 1e-10);
        assert!((t.data[4] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_add() {
        let a = Tensor::new(vec![1.0, 2.0], vec![2]).unwrap();
        let b = Tensor::new(vec![3.0, 4.0], vec![2]).unwrap();
        let c = a.add(&b).unwrap();
        assert_eq!(c.data, vec![4.0, 6.0]);
    }

    #[test]
    fn test_broadcast_add() {
        let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        let b = Tensor::new(vec![10.0, 20.0], vec![2]).unwrap();
        let c = a.add(&b).unwrap();
        assert_eq!(c.shape, vec![2, 2]);
        assert_eq!(c.data, vec![11.0, 22.0, 13.0, 24.0]);
    }

    #[test]
    fn test_matmul() {
        let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        let b = Tensor::new(vec![5.0, 6.0, 7.0, 8.0], vec![2, 2]).unwrap();
        let c = a.matmul(&b).unwrap();
        assert_eq!(c.shape, vec![2, 2]);
        // [1,2] @ [5,6] = [1*5+2*7, 1*6+2*8] = [19, 22]
        // [3,4]   [7,8]   [3*5+4*7, 3*6+4*8] = [43, 50]
        assert_eq!(c.data, vec![19.0, 22.0, 43.0, 50.0]);
    }

    #[test]
    fn test_transpose() {
        let a = Tensor::new(vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0], vec![2, 3]).unwrap();
        let b = a.transpose().unwrap();
        assert_eq!(b.shape, vec![3, 2]);
        assert_eq!(b.data, vec![1.0, 4.0, 2.0, 5.0, 3.0, 6.0]);
    }

    #[test]
    fn test_sum() {
        let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        assert_eq!(t.sum(), 10.0);
    }

    #[test]
    fn test_mean() {
        let t = Tensor::new(vec![1.0, 2.0, 3.0, 4.0], vec![2, 2]).unwrap();
        assert_eq!(t.mean(), 2.5);
    }

    #[test]
    fn test_reshape() {
        let a = Tensor::arange(0.0, 6.0, 1.0);
        let b = a.reshape(vec![2, 3]).unwrap();
        assert_eq!(b.shape, vec![2, 3]);
    }

    #[test]
    fn test_sigmoid() {
        let t = Tensor::new(vec![0.0], vec![1]).unwrap();
        let s = t.sigmoid();
        assert!((s.data[0] - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_relu() {
        let t = Tensor::new(vec![-1.0, 0.0, 1.0, 2.0], vec![4]).unwrap();
        let r = t.relu();
        assert_eq!(r.data, vec![0.0, 0.0, 1.0, 2.0]);
    }
}
