//! Tensor creation functions.

use crate::error::CompileError;
use super::core::{Tensor, compute_strides};

impl Tensor {
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
}
