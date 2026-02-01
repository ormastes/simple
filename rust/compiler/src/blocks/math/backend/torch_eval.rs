//! PyTorch tensor backend for math evaluation.
//!
//! When the `pytorch` feature is enabled, delegates tensor operations to
//! PyTorch via the runtime FFI. Otherwise, all operations fall back to CPU.

use crate::blocks::math::ast::MathExpr;
use crate::error::CompileError;
use crate::value::Value;

// ============================================================================
// Availability Detection
// ============================================================================

/// Check if PyTorch backend is available at runtime.
pub fn is_available() -> bool {
    #[cfg(feature = "pytorch")]
    { return simple_runtime::value::torch::creation::rt_torch_available() != 0; }
    #[cfg(not(feature = "pytorch"))]
    { false }
}

/// Alias matching runtime FFI naming convention.
pub fn rt_torch_available() -> bool { is_available() }

/// Check if PyTorch CUDA support is available at runtime.
pub fn is_cuda_available() -> bool {
    #[cfg(feature = "pytorch")]
    { return simple_runtime::value::torch::creation::rt_torch_cuda_available() != 0; }
    #[cfg(not(feature = "pytorch"))]
    { false }
}

/// Alias matching runtime FFI naming convention.
pub fn rt_torch_cuda_available() -> bool { is_cuda_available() }

/// Get the number of available CUDA devices.
pub fn cuda_device_count() -> i32 {
    #[cfg(feature = "pytorch")]
    { return simple_runtime::value::torch::creation::rt_torch_cuda_device_count(); }
    #[cfg(not(feature = "pytorch"))]
    { 0 }
}

/// Alias matching runtime FFI naming convention.
pub fn rt_torch_cuda_device_count() -> i32 { cuda_device_count() }

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluate a math expression using the PyTorch backend.
pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    evaluate_with_device(expr, 0)
}

/// Evaluate a math expression on a specific device.
///
/// Device codes: 0 = CPU, 1 = CUDA:0, 2 = CUDA:1, ...
pub fn evaluate_with_device(expr: &MathExpr, device: i32) -> Result<Value, CompileError> {
    if !is_available() {
        tracing::debug!("[math::backend::torch] Torch unavailable, falling back to CPU");
        return eval_cpu(expr);
    }

    tracing::debug!("[math::backend::torch] Evaluating on device={}", device);

    match expr {
        MathExpr::App(name, args) if is_torch_accelerated(name) => {
            tracing::debug!(
                "[math::backend::torch] Accelerating '{}' (device={})",
                name, device
            );
            eval_torch_function(name, args, device)
        }
        _ => eval_cpu(expr),
    }
}

/// Check if a function name can be accelerated by PyTorch.
fn is_torch_accelerated(name: &str) -> bool {
    matches!(
        name,
        "zeros" | "ones" | "randn" | "rand" | "arange"
            | "matmul" | "dot" | "transpose"
            | "relu" | "sigmoid" | "softmax" | "tanh"
    )
}

/// Evaluate a torch-accelerated function.
fn eval_torch_function(
    name: &str,
    args: &[MathExpr],
    device: i32,
) -> Result<Value, CompileError> {
    let eval_args: Vec<Value> = args
        .iter()
        .map(|a| eval_cpu(a))
        .collect::<Result<_, _>>()?;

    match name {
        "zeros" | "ones" | "randn" => eval_torch_create(&eval_args, device, name),
        _ => {
            tracing::debug!(
                "[math::backend::torch] '{}' not yet torch-wired, using CPU",
                name
            );
            let full_expr = MathExpr::App(name.to_string(), args.to_vec());
            eval_cpu(&full_expr)
        }
    }
}

/// Create a tensor via PyTorch FFI, then fall back to CPU result.
fn eval_torch_create(args: &[Value], _device: i32, func: &str) -> Result<Value, CompileError> {
    let shape = values_to_shape(args)?;

    // When pytorch feature is enabled, create tensor via FFI then free it.
    // Full tensor bridge (returning actual tensor data) is TBD.
    #[cfg(feature = "pytorch")]
    {
        use simple_runtime::value::torch::creation;
        let shape_i64: Vec<i64> = shape.iter().map(|&s| s as i64).collect();
        let ptr = shape_i64.as_ptr();
        let ndim = shape_i64.len() as i32;
        let handle = match func {
            "zeros" => creation::rt_torch_zeros(ptr, ndim, 0, _device),
            "ones" => creation::rt_torch_ones(ptr, ndim, 0, _device),
            "randn" => creation::rt_torch_randn(ptr, ndim, 0, _device),
            _ => 0,
        };
        if handle != 0 {
            creation::rt_torch_free(handle);
            tracing::debug!(
                "[math::backend::torch] {}: created torch tensor, using CPU result",
                func
            );
        }
    }

    let expr = MathExpr::App(
        func.to_string(),
        shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
    );
    eval_cpu(&expr)
}

// ============================================================================
// Helpers
// ============================================================================

fn eval_cpu(expr: &MathExpr) -> Result<Value, CompileError> {
    crate::blocks::math::eval::evaluate(expr)
}

fn values_to_shape(args: &[Value]) -> Result<Vec<usize>, CompileError> {
    args.iter()
        .map(|v| match v {
            Value::Int(n) if *n > 0 => Ok(*n as usize),
            Value::Float(f) if *f > 0.0 && f.fract() == 0.0 => Ok(*f as usize),
            _ => Err(crate::error::factory::invalid_tensor_shape()),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_availability_aliases() {
        assert_eq!(rt_torch_available(), is_available());
        assert_eq!(rt_torch_cuda_available(), is_cuda_available());
        assert_eq!(rt_torch_cuda_device_count(), cuda_device_count());
    }

    #[test]
    fn test_device_count_non_negative() {
        assert!(cuda_device_count() >= 0);
    }

    #[test]
    fn test_evaluate_basic() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(5));
    }

    #[test]
    fn test_evaluate_with_device() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        assert_eq!(evaluate_with_device(&expr, 0).unwrap(), Value::Int(12));
    }

    #[test]
    fn test_evaluate_zeros() {
        let expr = MathExpr::App("zeros".to_string(), vec![MathExpr::Int(3)]);
        if let Value::Array(arr) = evaluate(&expr).unwrap() {
            assert_eq!(arr.len(), 3);
        } else {
            panic!("expected array");
        }
    }

    #[test]
    fn test_is_torch_accelerated() {
        assert!(is_torch_accelerated("zeros"));
        assert!(is_torch_accelerated("matmul"));
        assert!(!is_torch_accelerated("sqrt"));
    }
}
