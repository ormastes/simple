//! CUDA computation backend for math evaluation.
//!
//! Provides direct CUDA computation via PyTorch's CUDA interface.
//! Detection delegates to `rt_torch_cuda_available()` from simple-runtime.
//!
//! When CUDA is unavailable, falls back to Torch, then CPU evaluation.

use crate::blocks::math::ast::MathExpr;
use crate::error::CompileError;
use crate::value::Value;

// ============================================================================
// Availability Detection
// ============================================================================

/// Check if CUDA backend is available at runtime.
///
/// Delegates to `rt_torch_cuda_available()` from simple-runtime.
pub fn is_available() -> bool {
    super::torch_eval::is_cuda_available()
}

/// Alias: `rt_cuda_available()` - short form.
pub fn rt_cuda_available() -> bool {
    is_available()
}

/// Get the number of CUDA devices available.
pub fn device_count() -> i32 {
    super::torch_eval::cuda_device_count()
}

/// Alias: `rt_cuda_device_count()` - short form.
pub fn rt_cuda_device_count() -> i32 {
    device_count()
}

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluate a math expression using the CUDA backend.
///
/// Falls back to Torch (CPU device), then CPU evaluation if CUDA is not available.
pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    evaluate_on_device(expr, 1) // device 1 = CUDA:0
}

/// Evaluate a math expression on a specific CUDA device.
///
/// Device codes (CUDA-specific):
/// - 1 = CUDA:0
/// - 2 = CUDA:1
/// - ...
///
/// Falls back to Torch CPU, then native CPU if the CUDA device is unavailable.
pub fn evaluate_on_device(expr: &MathExpr, device: i32) -> Result<Value, CompileError> {
    if !is_available() {
        tracing::debug!(
            "[math::backend::cuda] CUDA unavailable, falling back to Torch/CPU evaluation"
        );
        return super::torch_eval::evaluate(expr);
    }

    tracing::debug!(
        "[math::backend::cuda] Evaluating on CUDA device={} (1=CUDA:0, 2=CUDA:1, ...)",
        device
    );

    // Delegate to torch evaluator with CUDA device code
    super::torch_eval::evaluate_with_device(expr, device)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cuda_availability_matches_runtime() {
        let runtime_cuda =
            simple_runtime::value::torch::creation::rt_torch_cuda_available() != 0;
        assert_eq!(is_available(), runtime_cuda);
    }

    #[test]
    fn test_alias_rt_cuda_available() {
        assert_eq!(rt_cuda_available(), is_available());
    }

    #[test]
    fn test_device_count_non_negative() {
        assert!(device_count() >= 0);
    }

    #[test]
    fn test_evaluate_basic() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(12));
    }

    #[test]
    fn test_evaluate_on_device_fallback() {
        // Even if CUDA unavailable, should produce correct result via fallback
        let expr = MathExpr::Add(Box::new(MathExpr::Int(10)), Box::new(MathExpr::Int(5)));
        let result = evaluate_on_device(&expr, 1).unwrap();
        assert_eq!(result, Value::Int(15));
    }
}
