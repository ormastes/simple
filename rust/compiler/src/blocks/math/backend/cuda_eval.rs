//! CUDA computation backend for math evaluation (stub).
//!
//! CUDA is not linked in the default build. All operations fall back to CPU
//! via the torch_eval module.

use crate::blocks::math::ast::MathExpr;
use crate::error::CompileError;
use crate::value::Value;

pub fn is_available() -> bool {
    super::torch_eval::is_cuda_available()
}
pub fn rt_cuda_available() -> bool {
    is_available()
}
pub fn device_count() -> i32 {
    super::torch_eval::cuda_device_count()
}
pub fn rt_cuda_device_count() -> i32 {
    device_count()
}

// CUDA memory & device management (delegates to torch_eval)
pub fn memory_allocated(device: i32) -> i64 {
    super::torch_eval::cuda_memory_allocated(device)
}
pub fn rt_cuda_memory_allocated(device: i32) -> i64 {
    memory_allocated(device)
}
pub fn synchronize(device: i32) -> i32 {
    super::torch_eval::cuda_synchronize(device)
}
pub fn rt_cuda_synchronize(device: i32) -> i32 {
    synchronize(device)
}
pub fn reset_peak_memory_stats(device: i32) -> i32 {
    super::torch_eval::cuda_reset_peak_memory_stats(device)
}
pub fn rt_cuda_reset_peak_memory_stats(device: i32) -> i32 {
    reset_peak_memory_stats(device)
}

// Device transfer
pub fn to_cuda(tensor_handle: u64, device_id: i32) -> u64 {
    super::torch_eval::rt_torch_to_cuda(tensor_handle, device_id)
}
pub fn rt_cuda_to_device(tensor_handle: u64, device_id: i32) -> u64 {
    to_cuda(tensor_handle, device_id)
}

pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    evaluate_on_device(expr, 1)
}

pub fn evaluate_on_device(expr: &MathExpr, device: i32) -> Result<Value, CompileError> {
    if !is_available() {
        return super::torch_eval::evaluate(expr);
    }
    super::torch_eval::evaluate_with_device(expr, device)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_alias_rt_cuda_available() {
        assert_eq!(rt_cuda_available(), is_available());
    }

    #[test]
    fn test_evaluate_basic() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(12));
    }

    #[test]
    fn test_evaluate_on_device_fallback() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(10)), Box::new(MathExpr::Int(5)));
        assert_eq!(evaluate_on_device(&expr, 1).unwrap(), Value::Int(15));
    }
}
