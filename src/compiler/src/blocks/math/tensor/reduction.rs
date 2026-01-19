//! Reduction operations for tensors.

use crate::error::CompileError;
use super::core::Tensor;

impl Tensor {
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
}

/// Reduce along axis
pub(crate) fn reduce_axis<F>(tensor: &Tensor, axis: usize, reducer: F) -> Result<Tensor, CompileError>
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
