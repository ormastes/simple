//! Element-wise tensor operations.

use crate::error::CompileError;
use super::core::Tensor;
use super::broadcast::broadcast_binary_op;

impl Tensor {
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
        broadcast_binary_op(self, other, |a, b| if b == 0.0 { f64::NAN } else { a / b })
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
}
