//! Matrix operations for tensors.

use crate::error::CompileError;
use super::core::{Tensor, compute_strides};

impl Tensor {
    /// Matrix multiplication (2D tensors)
    pub fn matmul(&self, other: &Tensor) -> Result<Tensor, CompileError> {
        if self.ndim() != 2 || other.ndim() != 2 {
            return Err(CompileError::Semantic("matmul requires 2D tensors".to_string()));
        }

        let (m, k1) = (self.shape[0], self.shape[1]);
        let (k2, n) = (other.shape[0], other.shape[1]);

        if k1 != k2 {
            return Err(crate::error::factory::tensor_shape_mismatch(
                "matmul",
                &format!("({}, {}) @ ({}, {})", m, k1, k2, n)
            ));
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
            return Err(crate::error::factory::tensor_shape_mismatch(
                "dot",
                &format!("{} vs {}", self.shape[0], other.shape[0])
            ));
        }
        Ok(self.data.iter().zip(other.data.iter()).map(|(a, b)| a * b).sum())
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
            return Err(crate::error::factory::tensor_reshape_failed(self.data.len(), &new_shape));
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
            shape: if new_shape.is_empty() { vec![] } else { new_shape },
            strides,
        }
    }

    /// Unsqueeze: add dimension of size 1 at position
    pub fn unsqueeze(&self, dim: usize) -> Result<Tensor, CompileError> {
        if dim > self.shape.len() {
            return Err(crate::error::factory::tensor_dim_out_of_range(dim, self.shape.len()));
        }
        let mut new_shape = self.shape.clone();
        new_shape.insert(dim, 1);
        Tensor::new(self.data.clone(), new_shape)
    }
}
