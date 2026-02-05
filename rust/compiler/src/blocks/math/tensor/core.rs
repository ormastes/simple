//! Core Tensor struct and basic properties.

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
    /// Create tensor from flat data and shape
    pub fn new(data: Vec<f64>, shape: Vec<usize>) -> Result<Self, CompileError> {
        let expected_len: usize = shape.iter().product();
        if data.len() != expected_len {
            return Err(crate::error::factory::tensor_data_length_mismatch(
                data.len(),
                &shape,
                expected_len,
            ));
        }
        let strides = compute_strides(&shape);
        Ok(Self { data, shape, strides })
    }

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
            return Err(crate::error::factory::tensor_item_requires_scalar(self.data.len()));
        }
        Ok(self.data[0])
    }
}

/// Compute strides for row-major layout
pub(crate) fn compute_strides(shape: &[usize]) -> Vec<usize> {
    if shape.is_empty() {
        return vec![];
    }
    let mut strides = vec![1; shape.len()];
    for i in (0..shape.len() - 1).rev() {
        strides[i] = strides[i + 1] * shape[i + 1];
    }
    strides
}
