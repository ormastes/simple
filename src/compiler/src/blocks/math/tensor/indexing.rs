//! Indexing operations for tensors.

use crate::error::CompileError;
use super::core::Tensor;

impl Tensor {
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
