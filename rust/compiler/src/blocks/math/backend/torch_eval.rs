//! PyTorch tensor backend for math evaluation.
//!
//! When the `pytorch` feature is enabled, delegates tensor operations to
//! PyTorch via the runtime FFI. Otherwise, all operations fall back to CPU.
//!
//! Function names and parameter names match the core runtime library
//! (`simple_runtime::value::torch`) conventions:
//! - `shape_ptr: *const i64, ndim: i32` for shape parameters
//! - `dtype: i32` for dtype codes (0=f32, 1=f64, 2=i32, 3=i64)
//! - `device: i32` for device codes (0=CPU, 1=CUDA:0, 2=CUDA:1, ...)
//! - `tensor_handle: u64` for tensor handles
//! - `a_handle: u64, b_handle: u64` for binary tensor operations

use crate::blocks::math::ast::MathExpr;
use crate::error::CompileError;
use crate::value::Value;

// ============================================================================
// Availability Detection
// Matches: rt_torch_available(), rt_torch_cuda_available(),
//          rt_torch_cuda_device_count()
// ============================================================================

/// Check if PyTorch backend is available at runtime.
/// Wraps `rt_torch_available() -> i32` from simple-runtime.
pub fn is_available() -> bool {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_available() != 0;
    }
    #[cfg(not(feature = "pytorch"))]
    {
        false
    }
}

/// Alias: matches `rt_torch_available()` naming.
pub fn rt_torch_available() -> bool {
    is_available()
}

/// Check if PyTorch CUDA support is available at runtime.
/// Wraps `rt_torch_cuda_available() -> i32` from simple-runtime.
pub fn is_cuda_available() -> bool {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_cuda_available() != 0;
    }
    #[cfg(not(feature = "pytorch"))]
    {
        false
    }
}

/// Alias: matches `rt_torch_cuda_available()` naming.
pub fn rt_torch_cuda_available() -> bool {
    is_cuda_available()
}

/// Get the number of available CUDA devices.
/// Wraps `rt_torch_cuda_device_count() -> i32` from simple-runtime.
pub fn cuda_device_count() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_cuda_device_count();
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Alias: matches `rt_torch_cuda_device_count()` naming.
pub fn rt_torch_cuda_device_count() -> i32 {
    cuda_device_count()
}

// ============================================================================
// CUDA Memory & Device Management
// Matches: rt_torch_cuda_memory_allocated(device),
//          rt_torch_cuda_synchronize(device),
//          rt_torch_to_device(tensor_handle, device_code)
// ============================================================================

/// Get CUDA memory allocated on a device (bytes).
/// Wraps `rt_torch_cuda_memory_allocated(device: i32) -> i64`.
pub fn cuda_memory_allocated(device: i32) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_cuda_memory_allocated(device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        0
    }
}

/// Alias: matches `rt_torch_cuda_memory_allocated()` naming.
pub fn rt_torch_cuda_memory_allocated(device: i32) -> i64 {
    cuda_memory_allocated(device)
}

/// Synchronize a CUDA device.
/// Wraps `rt_torch_cuda_synchronize(device: i32) -> i32`.
pub fn cuda_synchronize(device: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_cuda_synchronize(device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        0
    }
}

/// Alias: matches `rt_torch_cuda_synchronize()` naming.
pub fn rt_torch_cuda_synchronize(device: i32) -> i32 {
    cuda_synchronize(device)
}

/// Reset peak memory stats on a CUDA device.
/// Wraps `rt_torch_cuda_reset_peak_memory_stats(device: i32) -> i32`.
pub fn cuda_reset_peak_memory_stats(device: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_cuda_reset_peak_memory_stats(device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        0
    }
}

/// Alias: matches `rt_torch_cuda_reset_peak_memory_stats()` naming.
pub fn rt_torch_cuda_reset_peak_memory_stats(device: i32) -> i32 {
    cuda_reset_peak_memory_stats(device)
}

// ============================================================================
// Tensor Creation Helpers
// Matches runtime param conventions:
//   shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32 -> u64
// ============================================================================

/// Create a zeros tensor. Returns handle (0 on failure).
/// Wraps `rt_torch_zeros(shape_ptr, ndim, dtype, device) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_zeros(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_zeros(shape_ptr, ndim, dtype, device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Create a ones tensor. Returns handle (0 on failure).
/// Wraps `rt_torch_ones(shape_ptr, ndim, dtype, device) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_ones(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_ones(shape_ptr, ndim, dtype, device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Create a randn tensor. Returns handle (0 on failure).
/// Wraps `rt_torch_randn(shape_ptr, ndim, dtype, device) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_randn(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_randn(shape_ptr, ndim, dtype, device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Create an arange tensor. Returns handle (0 on failure).
/// Wraps `rt_torch_arange(start, end, step, dtype, device) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_arange(start: i64, end: i64, step: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_arange(start, end, step, dtype, device);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Free a tensor handle.
/// Wraps `rt_torch_free(tensor_handle) -> i32`.
#[allow(unused_variables)]
pub fn rt_torch_free(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_free(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Clone a tensor. Returns new handle.
/// Wraps `rt_torch_clone(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_clone(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_clone(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Element-wise Operations
// Matches: rt_torch_add(a_handle, b_handle) -> u64, etc.
// ============================================================================

/// Element-wise add. Wraps `rt_torch_add(a_handle, b_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_add(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_add(a_handle, b_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Element-wise sub. Wraps `rt_torch_sub(a_handle, b_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_sub(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_sub(a_handle, b_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Element-wise mul. Wraps `rt_torch_mul(a_handle, b_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_mul(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_mul(a_handle, b_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Element-wise div. Wraps `rt_torch_div(a_handle, b_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_div(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_div(a_handle, b_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Power. Wraps `rt_torch_pow(tensor_handle, exp) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_pow(tensor_handle: u64, exp: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_pow(tensor_handle, exp);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Sqrt. Wraps `rt_torch_sqrt(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_sqrt(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_sqrt(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Exp. Wraps `rt_torch_exp(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_exp(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_exp(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Log. Wraps `rt_torch_log(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_log(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_log(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Matrix Operations
// Matches: rt_torch_matmul(a_handle, b_handle) -> u64, etc.
// ============================================================================

/// Matrix multiply. Wraps `rt_torch_matmul(a_handle, b_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_matmul(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_matmul(a_handle, b_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Transpose. Wraps `rt_torch_transpose(tensor_handle, dim0, dim1) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_transpose(tensor_handle: u64, dim0: i64, dim1: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_transpose(tensor_handle, dim0, dim1);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Activation Functions
// Matches: rt_torch_relu(tensor_handle) -> u64, etc.
// ============================================================================

/// ReLU. Wraps `rt_torch_relu(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_relu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_relu(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Sigmoid. Wraps `rt_torch_sigmoid(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_sigmoid(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_sigmoid(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Tanh. Wraps `rt_torch_tanh(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_tanh(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_tanh(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Softmax. Wraps `rt_torch_softmax(tensor_handle, dim) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_softmax(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_softmax(tensor_handle, dim);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// GELU. Wraps `rt_torch_gelu(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_gelu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_gelu(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// SiLU. Wraps `rt_torch_silu(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_silu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_silu(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Reduction Operations
// Matches: rt_torch_sum(tensor_handle) -> u64, etc.
// ============================================================================

/// Sum all elements. Wraps `rt_torch_sum(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_sum(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_sum(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Mean of all elements. Wraps `rt_torch_mean(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_mean(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_mean(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Scalar value. Wraps `rt_torch_item(tensor_handle) -> f64`.
#[allow(unused_variables)]
pub fn rt_torch_item(tensor_handle: u64) -> f64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_item(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0.0
    }
}

// ============================================================================
// Shape Operations
// Matches: rt_torch_reshape(tensor_handle, new_shape_ptr, ndim) -> u64
// ============================================================================

/// Reshape. Wraps `rt_torch_reshape(tensor_handle, new_shape_ptr, ndim) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_reshape(tensor_handle: u64, new_shape_ptr: *const i64, ndim: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_reshape(tensor_handle, new_shape_ptr, ndim);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Tensor Metadata
// Matches: rt_torch_shape, rt_torch_dtype, rt_torch_numel, rt_torch_device
// ============================================================================

/// Get tensor dtype code. Wraps `rt_torch_dtype(tensor_handle) -> i32`.
#[allow(unused_variables)]
pub fn rt_torch_dtype(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_dtype(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        -1
    }
}

/// Get tensor element count. Wraps `rt_torch_numel(tensor_handle) -> i64`.
#[allow(unused_variables)]
pub fn rt_torch_numel(tensor_handle: u64) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_numel(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Get tensor device code. Wraps `rt_torch_device(tensor_handle) -> i32`.
#[allow(unused_variables)]
pub fn rt_torch_device(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_device(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Device Transfer
// Matches: rt_torch_to_device, rt_torch_to_cpu, rt_torch_to_cuda
// ============================================================================

/// Move tensor to device. Wraps `rt_torch_to_device(tensor_handle, device_code) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_to_device(tensor_handle: u64, device_code: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_to_device(tensor_handle, device_code);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Move tensor to CPU. Wraps `rt_torch_to_cpu(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_to_cpu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_to_cpu(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Move tensor to CUDA. Wraps `rt_torch_to_cuda(tensor_handle, device_id) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_to_cuda(tensor_handle: u64, device_id: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_to_cuda(tensor_handle, device_id);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Autograd
// Matches: rt_torch_backward, rt_torch_grad, rt_torch_set_requires_grad, etc.
// ============================================================================

/// Run backward pass. Wraps `rt_torch_backward(tensor_handle) -> i32`.
#[allow(unused_variables)]
pub fn rt_torch_backward(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_backward(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        -1
    }
}

/// Get gradient tensor. Wraps `rt_torch_grad(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_grad(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_grad(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Set requires_grad. Wraps `rt_torch_set_requires_grad(tensor_handle, requires_grad) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_set_requires_grad(tensor_handle: u64, requires_grad: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_set_requires_grad(tensor_handle, requires_grad);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Detach from computation graph. Wraps `rt_torch_detach(tensor_handle) -> u64`.
#[allow(unused_variables)]
pub fn rt_torch_detach(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        return simple_runtime::value::torch::creation::rt_torch_detach(tensor_handle);
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// Evaluation (MathExpr → Value dispatch)
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
            tracing::debug!("[math::backend::torch] Accelerating '{}' (device={})", name, device);
            eval_torch_function(name, args, device)
        }
        _ => eval_cpu(expr),
    }
}

/// Check if a function name can be accelerated by PyTorch.
fn is_torch_accelerated(name: &str) -> bool {
    matches!(
        name,
        "zeros"
            | "ones"
            | "randn"
            | "rand"
            | "arange"
            | "matmul"
            | "dot"
            | "transpose"
            | "relu"
            | "sigmoid"
            | "softmax"
            | "tanh"
            | "gelu"
            | "silu"
    )
}

/// Evaluate a torch-accelerated function.
fn eval_torch_function(name: &str, args: &[MathExpr], device: i32) -> Result<Value, CompileError> {
    let eval_args: Vec<Value> = args.iter().map(|a| eval_cpu(a)).collect::<Result<_, _>>()?;

    match name {
        "zeros" | "ones" | "randn" => eval_torch_create(&eval_args, device, name),
        "arange" => eval_torch_arange(&eval_args, device),
        _ => {
            tracing::debug!("[math::backend::torch] '{}' not yet torch-wired, using CPU", name);
            let full_expr = MathExpr::App(name.to_string(), args.to_vec());
            eval_cpu(&full_expr)
        }
    }
}

/// Create a tensor via PyTorch FFI (zeros/ones/randn), then fall back to CPU result.
fn eval_torch_create(args: &[Value], device: i32, func: &str) -> Result<Value, CompileError> {
    let shape = values_to_shape(args)?;

    #[cfg(feature = "pytorch")]
    {
        let shape_i64: Vec<i64> = shape.iter().map(|&s| s as i64).collect();
        let shape_ptr = shape_i64.as_ptr();
        let ndim = shape_i64.len() as i32;
        let dtype = 0_i32; // f32
        let tensor_handle = match func {
            "zeros" => rt_torch_zeros(shape_ptr, ndim, dtype, device),
            "ones" => rt_torch_ones(shape_ptr, ndim, dtype, device),
            "randn" => rt_torch_randn(shape_ptr, ndim, dtype, device),
            _ => 0,
        };
        if tensor_handle != 0 {
            rt_torch_free(tensor_handle);
            tracing::debug!(
                "[math::backend::torch] {}: created torch tensor (device={}), using CPU result",
                func,
                device
            );
        }
    }
    let _ = device; // suppress unused warning without pytorch

    let expr = MathExpr::App(
        func.to_string(),
        shape.iter().map(|&s| MathExpr::Int(s as i64)).collect(),
    );
    eval_cpu(&expr)
}

/// Create an arange tensor via PyTorch FFI.
fn eval_torch_arange(args: &[Value], device: i32) -> Result<Value, CompileError> {
    let (start, end, step) = match args.len() {
        1 => (0i64, value_to_i64(&args[0])?, 1i64),
        2 => (value_to_i64(&args[0])?, value_to_i64(&args[1])?, 1i64),
        3 => (
            value_to_i64(&args[0])?,
            value_to_i64(&args[1])?,
            value_to_i64(&args[2])?,
        ),
        _ => return Err(crate::error::factory::invalid_tensor_shape()),
    };

    #[cfg(feature = "pytorch")]
    {
        let dtype = 3_i32; // i64
        let tensor_handle = rt_torch_arange(start, end, step, dtype, device);
        if tensor_handle != 0 {
            rt_torch_free(tensor_handle);
            tracing::debug!(
                "[math::backend::torch] arange({}, {}, {}) on device={}",
                start,
                end,
                step,
                device
            );
        }
    }
    let _ = device;

    let expr = MathExpr::App(
        "arange".to_string(),
        vec![MathExpr::Int(start), MathExpr::Int(end), MathExpr::Int(step)],
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

fn value_to_i64(v: &Value) -> Result<i64, CompileError> {
    match v {
        Value::Int(n) => Ok(*n),
        Value::Float(f) => Ok(*f as i64),
        _ => Err(crate::error::factory::invalid_tensor_shape()),
    }
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
    fn test_cuda_memory_non_negative() {
        assert!(cuda_memory_allocated(0) >= 0);
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
        assert!(is_torch_accelerated("relu"));
        assert!(is_torch_accelerated("gelu"));
        assert!(is_torch_accelerated("silu"));
        assert!(!is_torch_accelerated("sqrt"));
    }

    #[test]
    fn test_creation_stubs_without_pytorch() {
        // Without feature, all return 0
        #[cfg(not(feature = "pytorch"))]
        {
            let shape: Vec<i64> = vec![3];
            assert_eq!(rt_torch_zeros(shape.as_ptr(), 1, 0, 0), 0);
            assert_eq!(rt_torch_ones(shape.as_ptr(), 1, 0, 0), 0);
            assert_eq!(rt_torch_randn(shape.as_ptr(), 1, 0, 0), 0);
            assert_eq!(rt_torch_arange(0, 10, 1, 0, 0), 0);
            assert_eq!(rt_torch_free(0), 0);
            assert_eq!(rt_torch_clone(0), 0);
        }
    }

    #[test]
    fn test_op_stubs_without_pytorch() {
        #[cfg(not(feature = "pytorch"))]
        {
            assert_eq!(rt_torch_add(0, 0), 0);
            assert_eq!(rt_torch_sub(0, 0), 0);
            assert_eq!(rt_torch_mul(0, 0), 0);
            assert_eq!(rt_torch_div(0, 0), 0);
            assert_eq!(rt_torch_matmul(0, 0), 0);
            assert_eq!(rt_torch_relu(0), 0);
            assert_eq!(rt_torch_sigmoid(0), 0);
            assert_eq!(rt_torch_softmax(0, 0), 0);
            assert_eq!(rt_torch_sum(0), 0);
            assert_eq!(rt_torch_mean(0), 0);
        }
    }

    #[test]
    fn test_device_stubs_without_pytorch() {
        #[cfg(not(feature = "pytorch"))]
        {
            assert_eq!(rt_torch_to_device(0, 0), 0);
            assert_eq!(rt_torch_to_cpu(0), 0);
            assert_eq!(rt_torch_to_cuda(0, 0), 0);
        }
    }

    #[test]
    fn test_autograd_stubs_without_pytorch() {
        #[cfg(not(feature = "pytorch"))]
        {
            assert_eq!(rt_torch_backward(0), -1);
            assert_eq!(rt_torch_grad(0), 0);
            assert_eq!(rt_torch_set_requires_grad(0, 1), 0);
            assert_eq!(rt_torch_detach(0), 0);
        }
    }
}
