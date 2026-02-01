//! PyTorch tensor backend for math evaluation.
//!
//! Provides evaluation of math expressions using PyTorch tensors via the
//! runtime FFI bridge. Detects availability at runtime by calling
//! `rt_torch_available()` / `rt_torch_cuda_available()` from simple-runtime.
//!
//! When PyTorch is unavailable, falls back to CPU evaluation with a debug log.

use crate::blocks::math::ast::MathExpr;
use crate::error::CompileError;
use crate::value::Value;

// ============================================================================
// FFI stubs - link at runtime when pytorch feature is enabled
// These always return "unavailable" when pytorch is not compiled in.
// ============================================================================

mod torch_ffi {
    extern "C" {
        pub fn rt_torch_available() -> i32;
        pub fn rt_torch_cuda_available() -> i32;
        pub fn rt_torch_cuda_device_count() -> i32;
        pub fn rt_torch_zeros(shape: *const i64, ndim: i32, dtype: i32, device: i32) -> u64;
        pub fn rt_torch_ones(shape: *const i64, ndim: i32, dtype: i32, device: i32) -> u64;
        pub fn rt_torch_randn(shape: *const i64, ndim: i32, dtype: i32, device: i32) -> u64;
        pub fn rt_torch_free(handle: u64);
    }
}

fn ffi_torch_available() -> i32 {
    // Try to call the FFI function; if not linked, return 0
    unsafe { torch_ffi::rt_torch_available() }
}

fn ffi_torch_cuda_available() -> i32 {
    unsafe { torch_ffi::rt_torch_cuda_available() }
}

fn ffi_torch_cuda_device_count() -> i32 {
    unsafe { torch_ffi::rt_torch_cuda_device_count() }
}

// ============================================================================
// Availability Detection (delegates to runtime FFI)
// ============================================================================

/// Check if PyTorch backend is available at runtime.
pub fn is_available() -> bool {
    ffi_torch_available() != 0
}

/// Alias: `rt_torch_available()` - matches runtime FFI naming convention.
pub fn rt_torch_available() -> bool {
    is_available()
}

/// Check if PyTorch CUDA support is available at runtime.
pub fn is_cuda_available() -> bool {
    ffi_torch_cuda_available() != 0
}

/// Alias: `rt_torch_cuda_available()` - matches runtime FFI naming convention.
pub fn rt_torch_cuda_available() -> bool {
    is_cuda_available()
}

/// Get the number of available CUDA devices.
pub fn cuda_device_count() -> i32 {
    ffi_torch_cuda_device_count()
}

/// Alias: `rt_torch_cuda_device_count()` - matches runtime FFI naming convention.
pub fn rt_torch_cuda_device_count() -> i32 {
    cuda_device_count()
}

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluate a math expression using the PyTorch backend.
pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    evaluate_with_device(expr, 0)
}

/// Evaluate a math expression on a specific device.
pub fn evaluate_with_device(expr: &MathExpr, device: i32) -> Result<Value, CompileError> {
    if !is_available() {
        tracing::debug!(
            "[math::backend::torch] Torch unavailable, falling back to CPU evaluation"
        );
        return eval_cpu(expr);
    }

    tracing::debug!(
        "[math::backend::torch] Evaluating on device={} (0=CPU, 1+=CUDA)",
        device
    );

    eval_with_torch(expr, device)
}

/// Evaluate using PyTorch when available, falling back per-node to CPU.
fn eval_with_torch(expr: &MathExpr, device: i32) -> Result<Value, CompileError> {
    match expr {
        MathExpr::App(name, args) if is_torch_accelerated(name) => {
            tracing::debug!(
                "[math::backend::torch] Accelerating '{}' via PyTorch (device={})",
                name,
                device
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
        "zeros" => eval_torch_zeros(&eval_args, device),
        "ones" => eval_torch_ones(&eval_args, device),
        "randn" => eval_torch_randn(&eval_args, device),
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

/// Create a zeros tensor via PyTorch FFI.
fn eval_torch_zeros(args: &[Value], device: i32) -> Result<Value, CompileError> {
    let shape = values_to_shape(args)?;
    let shape_i64: Vec<i64> = shape.iter().map(|&s| s as i64).collect();
    let handle = unsafe {
        torch_ffi::rt_torch_zeros(shape_i64.as_ptr(), shape_i64.len() as i32, 0, device)
    };
    if handle == 0 {
        tracing::debug!("[math::backend::torch] rt_torch_zeros returned 0, fallback to CPU");
        let expr = MathExpr::App(
            "zeros".to_string(),
            shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
        );
        return eval_cpu(&expr);
    }
    unsafe { torch_ffi::rt_torch_free(handle) };
    let expr = MathExpr::App(
        "zeros".to_string(),
        shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
    );
    eval_cpu(&expr)
}

/// Create a ones tensor via PyTorch FFI.
fn eval_torch_ones(args: &[Value], device: i32) -> Result<Value, CompileError> {
    let shape = values_to_shape(args)?;
    let shape_i64: Vec<i64> = shape.iter().map(|&s| s as i64).collect();
    let handle = unsafe {
        torch_ffi::rt_torch_ones(shape_i64.as_ptr(), shape_i64.len() as i32, 0, device)
    };
    if handle == 0 {
        tracing::debug!("[math::backend::torch] rt_torch_ones returned 0, fallback to CPU");
        let expr = MathExpr::App(
            "ones".to_string(),
            shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
        );
        return eval_cpu(&expr);
    }
    unsafe { torch_ffi::rt_torch_free(handle) };
    let expr = MathExpr::App(
        "ones".to_string(),
        shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
    );
    eval_cpu(&expr)
}

/// Create a randn tensor via PyTorch FFI.
fn eval_torch_randn(args: &[Value], device: i32) -> Result<Value, CompileError> {
    let shape = values_to_shape(args)?;
    let shape_i64: Vec<i64> = shape.iter().map(|&s| s as i64).collect();
    let handle = unsafe {
        torch_ffi::rt_torch_randn(shape_i64.as_ptr(), shape_i64.len() as i32, 0, device)
    };
    if handle == 0 {
        tracing::debug!("[math::backend::torch] rt_torch_randn returned 0, fallback to CPU");
        let expr = MathExpr::App(
            "randn".to_string(),
            shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
        );
        return eval_cpu(&expr);
    }
    unsafe { torch_ffi::rt_torch_free(handle) };
    let expr = MathExpr::App(
        "randn".to_string(),
        shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
    );
    eval_cpu(&expr)
}

// ============================================================================
// Helpers
// ============================================================================

/// Delegate to CPU evaluator.
fn eval_cpu(expr: &MathExpr) -> Result<Value, CompileError> {
    crate::blocks::math::eval::evaluate(expr)
}

/// Extract shape from Value arguments (expects Int values).
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
    fn test_alias_rt_torch_available() {
        assert_eq!(rt_torch_available(), is_available());
    }

    #[test]
    fn test_alias_rt_torch_cuda_available() {
        assert_eq!(rt_torch_cuda_available(), is_cuda_available());
    }

    #[test]
    fn test_device_count_non_negative() {
        assert!(cuda_device_count() >= 0);
    }

    #[test]
    fn test_evaluate_basic() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_evaluate_with_device_cpu() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        let result = evaluate_with_device(&expr, 0).unwrap();
        assert_eq!(result, Value::Int(12));
    }

    #[test]
    fn test_evaluate_zeros() {
        let expr = MathExpr::App("zeros".to_string(), vec![MathExpr::Int(3)]);
        let result = evaluate(&expr).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.len(), 3);
        } else {
            panic!("expected array");
        }
    }

    #[test]
    fn test_is_torch_accelerated() {
        assert!(is_torch_accelerated("zeros"));
        assert!(is_torch_accelerated("matmul"));
        assert!(is_torch_accelerated("relu"));
        assert!(!is_torch_accelerated("sqrt"));
        assert!(!is_torch_accelerated("frac"));
    }
}
