//! Indexing operations for tensors.

use crate::error::CompileError;
use super::core::Tensor;

impl Tensor {
    /// Get element at index
    pub fn get(&self, indices: &[usize]) -> Result<f64, CompileError> {
        if indices.len() != self.shape.len() {
            return Err(crate::error::factory::tensor_index_count_mismatch(self.shape.len(), indices.len()));
        }
        let mut flat_idx = 0;
        for (i, &idx) in indices.iter().enumerate() {
            if idx >= self.shape[i] {
                return Err(crate::error::factory::tensor_index_out_of_bounds(idx, i, self.shape[i]));
            }
            flat_idx += idx * self.strides[i];
        }
        Ok(self.data[flat_idx])
    }

    /// Set element at index
    pub fn set(&mut self, indices: &[usize], value: f64) -> Result<(), CompileError> {
        if indices.len() != self.shape.len() {
            return Err(crate::error::factory::tensor_index_count_mismatch(self.shape.len(), indices.len()));
        }
        let mut flat_idx = 0;
        for (i, &idx) in indices.iter().enumerate() {
            if idx >= self.shape[i] {
                return Err(crate::error::factory::tensor_index_out_of_bounds(idx, i, self.shape[i]));
            }
            flat_idx += idx * self.strides[i];
        }
        self.data[flat_idx] = value;
        Ok(())
    }
}
