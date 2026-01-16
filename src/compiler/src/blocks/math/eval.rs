//! Math expression evaluator.
//!
//! Evaluates math AST to numeric values or tensors. Supports:
//! - Basic arithmetic (scalar and tensor)
//! - Trigonometric functions
//! - Logarithmic/exponential functions
//! - Special functions (factorial, binomial, etc.)
//! - Binders (sum, prod, int) with numeric evaluation
//! - Tensor operations (torch-compatible)

use super::ast::{get_constant, MathExpr, Range};
use super::tensor::Tensor;
use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;

/// Math evaluation result - can be scalar or tensor
#[derive(Debug, Clone)]
pub enum MathValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Tensor(Tensor),
}

impl MathValue {
    pub fn to_value(self) -> Value {
        match self {
            MathValue::Int(n) => Value::Int(n),
            MathValue::Float(f) => Value::Float(f),
            MathValue::Bool(b) => Value::Bool(b),
            MathValue::Tensor(t) => {
                // Convert tensor to Value::Array with nested structure
                tensor_to_value(&t)
            }
        }
    }

    pub fn as_f64(&self) -> Result<f64, CompileError> {
        match self {
            MathValue::Int(n) => Ok(*n as f64),
            MathValue::Float(f) => Ok(*f),
            MathValue::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            MathValue::Tensor(t) => t.item(),
        }
    }

    pub fn is_tensor(&self) -> bool {
        matches!(self, MathValue::Tensor(_))
    }
}

/// Convert tensor to nested Value::Array
fn tensor_to_value(tensor: &Tensor) -> Value {
    if tensor.shape.is_empty() {
        // Scalar tensor
        return Value::Float(tensor.data[0]);
    }

    if tensor.shape.len() == 1 {
        // 1D tensor -> simple array
        return Value::Array(tensor.data.iter().map(|&x| Value::Float(x)).collect());
    }

    // Multi-dimensional: build nested arrays
    fn build_nested(data: &[f64], shape: &[usize], offset: usize) -> Value {
        if shape.len() == 1 {
            Value::Array(data[offset..offset + shape[0]].iter().map(|&x| Value::Float(x)).collect())
        } else {
            let inner_size: usize = shape[1..].iter().product();
            Value::Array(
                (0..shape[0])
                    .map(|i| build_nested(data, &shape[1..], offset + i * inner_size))
                    .collect(),
            )
        }
    }

    build_nested(&tensor.data, &tensor.shape, 0)
}

/// Evaluate math expression to a Value
pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    let mut env = HashMap::new();
    let result = eval_with_env(expr, &mut env)?;
    Ok(result.to_value())
}

/// Evaluate with variable environment
fn eval_with_env(expr: &MathExpr, env: &mut HashMap<String, MathValue>) -> Result<MathValue, CompileError> {
    match expr {
        MathExpr::Int(n) => Ok(MathValue::Int(*n)),
        MathExpr::Float(f) => Ok(MathValue::Float(*f)),

        MathExpr::Array(elements) => {
            // Evaluate array to tensor
            let values: Vec<MathValue> = elements
                .iter()
                .map(|e| eval_with_env(e, env))
                .collect::<Result<_, _>>()?;

            // Check if all elements are scalars or all are arrays/tensors
            if values.is_empty() {
                return Ok(MathValue::Tensor(Tensor::zeros(vec![0])));
            }

            // Try to create tensor from nested structure
            let (data, shape) = flatten_to_tensor(&values)?;
            Ok(MathValue::Tensor(Tensor::new(data, shape)?))
        }

        MathExpr::Var(name) => {
            // Check environment first
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            // Then check built-in constants
            if let Some(val) = get_constant(name) {
                return Ok(MathValue::Float(val));
            }
            // Unknown variable - return as error
            Err(CompileError::Semantic(format!(
                "undefined math variable: {}",
                name
            )))
        }

        MathExpr::Add(left, right) => {
            let l = eval_with_env(left, env)?;
            let r = eval_with_env(right, env)?;
            binary_op(&l, &r, |a, b| a + b, "add")
        }

        MathExpr::Sub(left, right) => {
            let l = eval_with_env(left, env)?;
            let r = eval_with_env(right, env)?;
            binary_op(&l, &r, |a, b| a - b, "sub")
        }

        MathExpr::Mul(left, right) => {
            let l = eval_with_env(left, env)?;
            let r = eval_with_env(right, env)?;
            binary_op(&l, &r, |a, b| a * b, "mul")
        }

        MathExpr::Div(left, right) => {
            let l = eval_with_env(left, env)?;
            let r = eval_with_env(right, env)?;
            binary_op(&l, &r, |a, b| if b == 0.0 { f64::NAN } else { a / b }, "div")
        }

        MathExpr::Pow(base, exp) => {
            let b = eval_with_env(base, env)?;
            let e = eval_with_env(exp, env)?;
            // Power operations always return Float (transcendental operation)
            match (&b, &e) {
                (MathValue::Tensor(a), MathValue::Tensor(b)) => {
                    Ok(MathValue::Tensor(a.pow(b)?))
                }
                (MathValue::Tensor(t), scalar) => {
                    let s = scalar.as_f64()?;
                    // t^s element-wise
                    let data: Vec<f64> = t.data.iter().map(|&x| x.powf(s)).collect();
                    Ok(MathValue::Tensor(Tensor::new(data, t.shape.clone())?))
                }
                (scalar, MathValue::Tensor(t)) => {
                    let s = scalar.as_f64()?;
                    // s^t element-wise
                    let data: Vec<f64> = t.data.iter().map(|&x| s.powf(x)).collect();
                    Ok(MathValue::Tensor(Tensor::new(data, t.shape.clone())?))
                }
                _ => {
                    let base_f = b.as_f64()?;
                    let exp_f = e.as_f64()?;
                    Ok(MathValue::Float(base_f.powf(exp_f)))
                }
            }
        }

        MathExpr::Mod(left, right) => {
            let l = eval_with_env(left, env)?;
            let r = eval_with_env(right, env)?;
            binary_op(&l, &r, |a, b| if b == 0.0 { f64::NAN } else { a % b }, "mod")
        }

        MathExpr::Neg(inner) => {
            let val = eval_with_env(inner, env)?;
            unary_op(&val, |x| -x)
        }

        MathExpr::Abs(inner) => {
            let val = eval_with_env(inner, env)?;
            unary_op(&val, |x| x.abs())
        }

        MathExpr::App(name, args) => eval_function(name, args, env),

        MathExpr::Subscript(base, index) => {
            let b = eval_with_env(base, env)?;
            let idx = eval_with_env(index, env)?;

            match (&b, &idx) {
                (MathValue::Tensor(t), MathValue::Int(i)) => {
                    if t.ndim() == 1 {
                        let i = *i as usize;
                        if i >= t.shape[0] {
                            return Err(CompileError::Semantic(format!(
                                "index {} out of bounds for tensor of length {}",
                                i, t.shape[0]
                            )));
                        }
                        Ok(MathValue::Float(t.data[i]))
                    } else {
                        // For multi-dim, return slice
                        let i = *i as usize;
                        let inner_size: usize = t.shape[1..].iter().product();
                        let start = i * inner_size;
                        let data = t.data[start..start + inner_size].to_vec();
                        Ok(MathValue::Tensor(Tensor::new(data, t.shape[1..].to_vec())?))
                    }
                }
                _ => {
                    // For non-tensors, just evaluate base
                    Ok(b)
                }
            }
        }

        MathExpr::Group(inner) => eval_with_env(inner, env),

        MathExpr::Sum { var, range, body } => eval_sum(var, range, body, env),

        MathExpr::Prod { var, range, body } => eval_prod(var, range, body, env),

        MathExpr::Integral { var, range, body } => eval_integral(var, range, body, env),

        // Comparisons return boolean
        MathExpr::Eq(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool((l - r).abs() < 1e-10))
        }

        MathExpr::Neq(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool((l - r).abs() >= 1e-10))
        }

        MathExpr::Lt(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool(l < r))
        }

        MathExpr::Le(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool(l <= r))
        }

        MathExpr::Gt(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool(l > r))
        }

        MathExpr::Ge(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            Ok(MathValue::Bool(l >= r))
        }

        MathExpr::Approx(left, right) => {
            let l = eval_with_env(left, env)?.as_f64()?;
            let r = eval_with_env(right, env)?.as_f64()?;
            let tolerance = (l.abs() + r.abs()) * 0.01;
            Ok(MathValue::Bool((l - r).abs() <= tolerance.max(1e-10)))
        }
    }
}

/// Flatten nested MathValues to tensor data and shape
fn flatten_to_tensor(values: &[MathValue]) -> Result<(Vec<f64>, Vec<usize>), CompileError> {
    if values.is_empty() {
        return Ok((vec![], vec![0]));
    }

    // Check first element to determine structure
    match &values[0] {
        MathValue::Int(_) | MathValue::Float(_) | MathValue::Bool(_) => {
            // All elements should be scalars
            let data: Vec<f64> = values
                .iter()
                .map(|v| v.as_f64())
                .collect::<Result<_, _>>()?;
            Ok((data, vec![values.len()]))
        }
        MathValue::Tensor(t) => {
            // All elements should be tensors of same shape
            let inner_shape = t.shape.clone();
            let mut data = Vec::new();

            for v in values {
                match v {
                    MathValue::Tensor(t2) => {
                        if t2.shape != inner_shape {
                            return Err(CompileError::Semantic(
                                "inconsistent shapes in nested array".to_string(),
                            ));
                        }
                        data.extend(&t2.data);
                    }
                    _ => {
                        return Err(CompileError::Semantic(
                            "mixed scalar and tensor in array".to_string(),
                        ));
                    }
                }
            }

            let mut shape = vec![values.len()];
            shape.extend(inner_shape);
            Ok((data, shape))
        }
    }
}

/// Apply binary operation with broadcasting
fn binary_op<F>(left: &MathValue, right: &MathValue, op: F, _name: &str) -> Result<MathValue, CompileError>
where
    F: Fn(f64, f64) -> f64,
{
    match (left, right) {
        // Scalar ops
        (MathValue::Int(a), MathValue::Int(b)) => {
            let result = op(*a as f64, *b as f64);
            Ok(float_or_int_math(result))
        }
        (MathValue::Float(a), MathValue::Float(b)) => Ok(MathValue::Float(op(*a, *b))),
        (MathValue::Int(a), MathValue::Float(b)) => Ok(MathValue::Float(op(*a as f64, *b))),
        (MathValue::Float(a), MathValue::Int(b)) => Ok(MathValue::Float(op(*a, *b as f64))),

        // Tensor ops
        (MathValue::Tensor(a), MathValue::Tensor(b)) => {
            let result = broadcast_tensor_op(a, b, &op)?;
            Ok(MathValue::Tensor(result))
        }
        (MathValue::Tensor(t), scalar) | (scalar, MathValue::Tensor(t)) => {
            let s = scalar.as_f64()?;
            let scalar_tensor = Tensor::scalar(s);
            let (a, b) = if matches!(left, MathValue::Tensor(_)) {
                (t, &scalar_tensor)
            } else {
                (&scalar_tensor, t)
            };
            let result = broadcast_tensor_op(a, b, &op)?;
            Ok(MathValue::Tensor(result))
        }

        // Bool conversions
        (MathValue::Bool(a), b) => {
            let a_val = if *a { 1.0 } else { 0.0 };
            binary_op(&MathValue::Float(a_val), b, op, _name)
        }
        (a, MathValue::Bool(b)) => {
            let b_val = if *b { 1.0 } else { 0.0 };
            binary_op(a, &MathValue::Float(b_val), op, _name)
        }
    }
}

/// Broadcast tensor operation
fn broadcast_tensor_op<F>(a: &Tensor, b: &Tensor, op: F) -> Result<Tensor, CompileError>
where
    F: Fn(f64, f64) -> f64,
{
    // Simple case: same shape
    if a.shape == b.shape {
        let data: Vec<f64> = a.data.iter().zip(b.data.iter()).map(|(&x, &y)| op(x, y)).collect();
        return Tensor::new(data, a.shape.clone());
    }

    // Use tensor's broadcasting
    let scalar_a = Tensor::new(a.data.clone(), a.shape.clone())?;
    let scalar_b = Tensor::new(b.data.clone(), b.shape.clone())?;

    // Manual broadcast
    let result_shape = broadcast_shapes(&a.shape, &b.shape)?;
    let result_size: usize = result_shape.iter().product();
    let mut result_data = vec![0.0; result_size];

    for i in 0..result_size {
        let a_idx = broadcast_index(i, &result_shape, &a.shape);
        let b_idx = broadcast_index(i, &result_shape, &b.shape);
        result_data[i] = op(scalar_a.data[a_idx], scalar_b.data[b_idx]);
    }

    Tensor::new(result_data, result_shape)
}

/// Compute broadcast shapes
fn broadcast_shapes(a: &[usize], b: &[usize]) -> Result<Vec<usize>, CompileError> {
    let max_len = a.len().max(b.len());
    let mut result = vec![0; max_len];

    for i in 0..max_len {
        let a_dim = if i < max_len - a.len() { 1 } else { a[i - (max_len - a.len())] };
        let b_dim = if i < max_len - b.len() { 1 } else { b[i - (max_len - b.len())] };

        if a_dim == b_dim {
            result[i] = a_dim;
        } else if a_dim == 1 {
            result[i] = b_dim;
        } else if b_dim == 1 {
            result[i] = a_dim;
        } else {
            return Err(CompileError::Semantic(format!(
                "cannot broadcast shapes {:?} and {:?}",
                a, b
            )));
        }
    }

    Ok(result)
}

/// Compute index in source array for broadcast
fn broadcast_index(flat_idx: usize, result_shape: &[usize], source_shape: &[usize]) -> usize {
    let offset = result_shape.len() - source_shape.len();
    let mut source_idx = 0;
    let mut remaining = flat_idx;

    let result_strides: Vec<usize> = {
        let mut s = vec![1; result_shape.len()];
        for i in (0..result_shape.len() - 1).rev() {
            s[i] = s[i + 1] * result_shape[i + 1];
        }
        s
    };

    let source_strides: Vec<usize> = {
        let mut s = vec![1; source_shape.len()];
        for i in (0..source_shape.len() - 1).rev() {
            s[i] = s[i + 1] * source_shape[i + 1];
        }
        s
    };

    for (i, &stride) in result_strides.iter().enumerate() {
        let coord = remaining / stride;
        remaining %= stride;

        if i >= offset {
            let src_i = i - offset;
            let src_coord = if source_shape[src_i] == 1 { 0 } else { coord };
            source_idx += src_coord * source_strides[src_i];
        }
    }

    source_idx
}

/// Apply unary operation
fn unary_op<F>(val: &MathValue, op: F) -> Result<MathValue, CompileError>
where
    F: Fn(f64) -> f64,
{
    match val {
        MathValue::Int(n) => Ok(float_or_int_math(op(*n as f64))),
        MathValue::Float(f) => Ok(MathValue::Float(op(*f))),
        MathValue::Bool(b) => Ok(MathValue::Float(op(if *b { 1.0 } else { 0.0 }))),
        MathValue::Tensor(t) => {
            let data: Vec<f64> = t.data.iter().map(|&x| op(x)).collect();
            Ok(MathValue::Tensor(Tensor::new(data, t.shape.clone())?))
        }
    }
}

/// Convert f64 to Int or Float based on whether it's a whole number
fn float_or_int_math(val: f64) -> MathValue {
    if val.fract() == 0.0 && val.abs() < i64::MAX as f64 {
        MathValue::Int(val as i64)
    } else {
        MathValue::Float(val)
    }
}

/// Evaluate built-in function
fn eval_function(
    name: &str,
    args: &[MathExpr],
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    // Evaluate all arguments first
    let eval_args: Vec<MathValue> = args
        .iter()
        .map(|a| eval_with_env(a, env))
        .collect::<Result<_, _>>()?;

    match name {
        // ==========================================================================
        // Tensor creation functions
        // ==========================================================================
        "tensor" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("tensor requires 1 argument".into()));
            }
            match &eval_args[0] {
                MathValue::Tensor(t) => Ok(MathValue::Tensor(t.clone())),
                _ => {
                    let val = eval_args[0].as_f64()?;
                    Ok(MathValue::Tensor(Tensor::scalar(val)))
                }
            }
        }

        "zeros" => {
            let shape = args_to_shape(&eval_args)?;
            Ok(MathValue::Tensor(Tensor::zeros(shape)))
        }

        "ones" => {
            let shape = args_to_shape(&eval_args)?;
            Ok(MathValue::Tensor(Tensor::ones(shape)))
        }

        "full" => {
            if eval_args.len() < 2 {
                return Err(CompileError::Semantic("full requires shape and fill value".into()));
            }
            let fill = eval_args.last().unwrap().as_f64()?;
            let shape = args_to_shape(&eval_args[..eval_args.len() - 1])?;
            Ok(MathValue::Tensor(Tensor::full(shape, fill)))
        }

        "eye" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("eye requires 1 argument".into()));
            }
            let n = eval_args[0].as_f64()? as usize;
            Ok(MathValue::Tensor(Tensor::eye(n)))
        }

        "arange" => {
            let (start, end, step) = match eval_args.len() {
                1 => (0.0, eval_args[0].as_f64()?, 1.0),
                2 => (eval_args[0].as_f64()?, eval_args[1].as_f64()?, 1.0),
                3 => (eval_args[0].as_f64()?, eval_args[1].as_f64()?, eval_args[2].as_f64()?),
                _ => return Err(CompileError::Semantic("arange takes 1-3 arguments".into())),
            };
            Ok(MathValue::Tensor(Tensor::arange(start, end, step)))
        }

        "linspace" => {
            if eval_args.len() != 3 {
                return Err(CompileError::Semantic("linspace requires 3 arguments".into()));
            }
            let start = eval_args[0].as_f64()?;
            let end = eval_args[1].as_f64()?;
            let steps = eval_args[2].as_f64()? as usize;
            Ok(MathValue::Tensor(Tensor::linspace(start, end, steps)))
        }

        "rand" => {
            let shape = args_to_shape(&eval_args)?;
            Ok(MathValue::Tensor(Tensor::rand(shape)))
        }

        "randn" => {
            let shape = args_to_shape(&eval_args)?;
            Ok(MathValue::Tensor(Tensor::randn(shape)))
        }

        // ==========================================================================
        // Tensor operations
        // ==========================================================================
        "matmul" => {
            require_tensor_args(name, &eval_args, 2)?;
            let a = get_tensor(&eval_args[0])?;
            let b = get_tensor(&eval_args[1])?;
            Ok(MathValue::Tensor(a.matmul(&b)?))
        }

        "dot" => {
            require_tensor_args(name, &eval_args, 2)?;
            let a = get_tensor(&eval_args[0])?;
            let b = get_tensor(&eval_args[1])?;
            Ok(MathValue::Float(a.dot(&b)?))
        }

        "transpose" | "T" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Tensor(t.transpose()?))
        }

        "reshape" => {
            if eval_args.len() < 2 {
                return Err(CompileError::Semantic("reshape requires tensor and shape".into()));
            }
            let t = get_tensor(&eval_args[0])?;
            let shape = args_to_shape(&eval_args[1..])?;
            Ok(MathValue::Tensor(t.reshape(shape)?))
        }

        "flatten" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Tensor(t.flatten()))
        }

        "squeeze" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Tensor(t.squeeze()))
        }

        "unsqueeze" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("unsqueeze requires tensor and dim".into()));
            }
            let t = get_tensor(&eval_args[0])?;
            let dim = eval_args[1].as_f64()? as usize;
            Ok(MathValue::Tensor(t.unsqueeze(dim)?))
        }

        // ==========================================================================
        // Tensor properties
        // ==========================================================================
        "shape" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            let shape_data: Vec<f64> = t.shape.iter().map(|&s| s as f64).collect();
            Ok(MathValue::Tensor(Tensor::new(shape_data.clone(), vec![shape_data.len()])?))
        }

        "ndim" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Int(t.ndim() as i64))
        }

        "numel" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Int(t.numel() as i64))
        }

        "item" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Float(t.item()?))
        }

        // ==========================================================================
        // Tensor reductions
        // ==========================================================================
        "sum" if eval_args.len() == 1 && eval_args[0].is_tensor() => {
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Float(t.sum()))
        }

        "mean" => {
            if eval_args.len() == 1 && eval_args[0].is_tensor() {
                let t = get_tensor(&eval_args[0])?;
                Ok(MathValue::Float(t.mean()))
            } else {
                // Mean of arguments
                let vals: Vec<f64> = eval_args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
                if vals.is_empty() {
                    return Err(CompileError::Semantic("mean requires at least 1 argument".into()));
                }
                Ok(MathValue::Float(vals.iter().sum::<f64>() / vals.len() as f64))
            }
        }

        "var" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Float(t.var()))
        }

        "std" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Float(t.std()))
        }

        "argmin" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Int(t.argmin() as i64))
        }

        "argmax" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            Ok(MathValue::Int(t.argmax() as i64))
        }

        // ==========================================================================
        // Activation functions (element-wise)
        // ==========================================================================
        "relu" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("relu requires 1 argument".into()));
            }
            match &eval_args[0] {
                MathValue::Tensor(t) => Ok(MathValue::Tensor(t.relu())),
                v => {
                    let x = v.as_f64()?;
                    Ok(MathValue::Float(x.max(0.0)))
                }
            }
        }

        "sigmoid" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("sigmoid requires 1 argument".into()));
            }
            match &eval_args[0] {
                MathValue::Tensor(t) => Ok(MathValue::Tensor(t.sigmoid())),
                v => {
                    let x = v.as_f64()?;
                    Ok(MathValue::Float(1.0 / (1.0 + (-x).exp())))
                }
            }
        }

        "softmax" => {
            require_tensor_args(name, &eval_args, 1)?;
            let t = get_tensor(&eval_args[0])?;
            // Compute softmax (for 1D or last dim)
            let max_val = t.max();
            let exp_data: Vec<f64> = t.data.iter().map(|&x| (x - max_val).exp()).collect();
            let sum: f64 = exp_data.iter().sum();
            let softmax_data: Vec<f64> = exp_data.iter().map(|&x| x / sum).collect();
            Ok(MathValue::Tensor(Tensor::new(softmax_data, t.shape.clone())?))
        }

        "tanh" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("tanh requires 1 argument".into()));
            }
            match &eval_args[0] {
                MathValue::Tensor(t) => Ok(MathValue::Tensor(t.tanh())),
                v => {
                    let x = v.as_f64()?;
                    Ok(MathValue::Float(x.tanh()))
                }
            }
        }

        // ==========================================================================
        // Standard math functions (scalar, work element-wise on tensors)
        // ==========================================================================
        "sqrt" | "√" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("sqrt requires 1 argument".into()));
            }
            match &eval_args[0] {
                MathValue::Tensor(t) => Ok(MathValue::Tensor(t.sqrt())),
                v => {
                    let x = v.as_f64()?;
                    if x < 0.0 {
                        return Err(CompileError::Semantic("cannot take sqrt of negative".into()));
                    }
                    Ok(MathValue::Float(x.sqrt()))
                }
            }
        }

        "cbrt" => unary_math_fn(&eval_args, |x| x.cbrt()),
        "abs" => unary_math_fn(&eval_args, |x| x.abs()),
        "floor" => unary_math_fn(&eval_args, |x| x.floor()),
        "ceil" => unary_math_fn(&eval_args, |x| x.ceil()),
        "round" => unary_math_fn(&eval_args, |x| x.round()),
        "trunc" => unary_math_fn(&eval_args, |x| x.trunc()),
        "sign" | "sgn" => unary_math_fn(&eval_args, |x| x.signum()),
        "exp" => unary_math_fn(&eval_args, |x| x.exp()),
        "log" | "ln" => unary_math_fn(&eval_args, |x| x.ln()),
        "log10" => unary_math_fn(&eval_args, |x| x.log10()),
        "log2" => unary_math_fn(&eval_args, |x| x.log2()),
        "sin" => unary_math_fn(&eval_args, |x| x.sin()),
        "cos" => unary_math_fn(&eval_args, |x| x.cos()),
        "tan" => unary_math_fn(&eval_args, |x| x.tan()),
        "asin" | "arcsin" => unary_math_fn(&eval_args, |x| x.asin()),
        "acos" | "arccos" => unary_math_fn(&eval_args, |x| x.acos()),
        "atan" | "arctan" => unary_math_fn(&eval_args, |x| x.atan()),
        "sinh" => unary_math_fn(&eval_args, |x| x.sinh()),
        "cosh" => unary_math_fn(&eval_args, |x| x.cosh()),
        "asinh" => unary_math_fn(&eval_args, |x| x.asinh()),
        "acosh" => unary_math_fn(&eval_args, |x| x.acosh()),
        "atanh" => unary_math_fn(&eval_args, |x| x.atanh()),

        // ==========================================================================
        // Multi-arg math functions
        // ==========================================================================
        "frac" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("frac requires 2 arguments".into()));
            }
            let num = eval_args[0].as_f64()?;
            let denom = eval_args[1].as_f64()?;
            if denom == 0.0 {
                return Err(CompileError::Semantic("division by zero".into()));
            }
            Ok(MathValue::Float(num / denom))
        }

        "root" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("root requires 2 arguments".into()));
            }
            let n = eval_args[0].as_f64()?;
            let x = eval_args[1].as_f64()?;
            Ok(MathValue::Float(x.powf(1.0 / n)))
        }

        "min" => {
            if eval_args.is_empty() {
                return Err(CompileError::Semantic("min requires at least 1 argument".into()));
            }
            if eval_args.len() == 1 && eval_args[0].is_tensor() {
                let t = get_tensor(&eval_args[0])?;
                return Ok(MathValue::Float(t.min()));
            }
            let vals: Vec<f64> = eval_args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
            Ok(MathValue::Float(vals.into_iter().fold(f64::INFINITY, f64::min)))
        }

        "max" => {
            if eval_args.is_empty() {
                return Err(CompileError::Semantic("max requires at least 1 argument".into()));
            }
            if eval_args.len() == 1 && eval_args[0].is_tensor() {
                let t = get_tensor(&eval_args[0])?;
                return Ok(MathValue::Float(t.max()));
            }
            let vals: Vec<f64> = eval_args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
            Ok(MathValue::Float(vals.into_iter().fold(f64::NEG_INFINITY, f64::max)))
        }

        "gcd" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("gcd requires 2 arguments".into()));
            }
            let a = eval_args[0].as_f64()? as i64;
            let b = eval_args[1].as_f64()? as i64;
            Ok(MathValue::Int(gcd(a.abs(), b.abs())))
        }

        "lcm" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("lcm requires 2 arguments".into()));
            }
            let a = eval_args[0].as_f64()? as i64;
            let b = eval_args[1].as_f64()? as i64;
            if a == 0 || b == 0 {
                return Ok(MathValue::Int(0));
            }
            Ok(MathValue::Int((a.abs() / gcd(a.abs(), b.abs())) * b.abs()))
        }

        "factorial" | "fact" => {
            if eval_args.len() != 1 {
                return Err(CompileError::Semantic("factorial requires 1 argument".into()));
            }
            let n = eval_args[0].as_f64()? as i64;
            if n < 0 {
                return Err(CompileError::Semantic("factorial of negative".into()));
            }
            if n > 20 {
                Ok(MathValue::Float(gamma(n as f64 + 1.0)))
            } else {
                Ok(MathValue::Int(factorial(n as u64) as i64))
            }
        }

        "binomial" | "binom" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("binomial requires 2 arguments".into()));
            }
            let n = eval_args[0].as_f64()? as i64;
            let k = eval_args[1].as_f64()? as i64;
            if k < 0 || k > n {
                return Ok(MathValue::Int(0));
            }
            Ok(MathValue::Int(binomial(n as u64, k as u64) as i64))
        }

        "atan2" => {
            if eval_args.len() != 2 {
                return Err(CompileError::Semantic("atan2 requires 2 arguments".into()));
            }
            let y = eval_args[0].as_f64()?;
            let x = eval_args[1].as_f64()?;
            Ok(MathValue::Float(y.atan2(x)))
        }

        _ => Err(CompileError::Semantic(format!("unknown math function: {}", name))),
    }
}

/// Helper for unary math functions
fn unary_math_fn<F>(args: &[MathValue], op: F) -> Result<MathValue, CompileError>
where
    F: Fn(f64) -> f64,
{
    if args.len() != 1 {
        return Err(CompileError::Semantic("function requires 1 argument".into()));
    }
    match &args[0] {
        MathValue::Tensor(t) => {
            let data: Vec<f64> = t.data.iter().map(|&x| op(x)).collect();
            Ok(MathValue::Tensor(Tensor::new(data, t.shape.clone())?))
        }
        v => Ok(MathValue::Float(op(v.as_f64()?))),
    }
}

/// Convert args to shape vector
fn args_to_shape(args: &[MathValue]) -> Result<Vec<usize>, CompileError> {
    if args.len() == 1 {
        // Could be a single int or a tensor/array of ints
        match &args[0] {
            MathValue::Tensor(t) => {
                return Ok(t.data.iter().map(|&x| x as usize).collect());
            }
            _ => {}
        }
    }
    args.iter()
        .map(|a| {
            let v = a.as_f64()? as i64;
            if v < 0 {
                Err(CompileError::Semantic("shape dimensions must be non-negative".into()))
            } else {
                Ok(v as usize)
            }
        })
        .collect()
}

/// Require tensor arguments
fn require_tensor_args(name: &str, args: &[MathValue], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::Semantic(format!(
            "{} requires {} argument(s), got {}",
            name, expected, args.len()
        )));
    }
    Ok(())
}

/// Get tensor from MathValue, converting scalars
fn get_tensor(val: &MathValue) -> Result<Tensor, CompileError> {
    match val {
        MathValue::Tensor(t) => Ok(t.clone()),
        v => Ok(Tensor::scalar(v.as_f64()?)),
    }
}

/// Evaluate summation: sum(i, a..b) body
fn eval_sum(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    let start = eval_with_env(&range.start, env)?.as_f64()? as i64;
    let end = eval_with_env(&range.end, env)?.as_f64()? as i64;

    let mut total = 0.0;
    for i in start..=end {
        env.insert(var.to_string(), MathValue::Float(i as f64));
        total += eval_with_env(body, env)?.as_f64()?;
    }
    env.remove(var);

    Ok(float_or_int_math(total))
}

/// Evaluate product: prod(i, a..b) body
fn eval_prod(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    let start = eval_with_env(&range.start, env)?.as_f64()? as i64;
    let end = eval_with_env(&range.end, env)?.as_f64()? as i64;

    let mut product = 1.0;
    for i in start..=end {
        env.insert(var.to_string(), MathValue::Float(i as f64));
        product *= eval_with_env(body, env)?.as_f64()?;
    }
    env.remove(var);

    Ok(float_or_int_math(product))
}

/// Evaluate integral using Simpson's rule
fn eval_integral(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    let a = eval_with_env(&range.start, env)?.as_f64()?;
    let b = eval_with_env(&range.end, env)?.as_f64()?;

    let n = 1000;
    let h = (b - a) / n as f64;

    let eval_at = |x: f64, env: &mut HashMap<String, MathValue>| -> Result<f64, CompileError> {
        env.insert(var.to_string(), MathValue::Float(x));
        eval_with_env(body, env)?.as_f64()
    };

    let mut sum = eval_at(a, env)? + eval_at(b, env)?;

    for i in 1..n {
        let x = a + i as f64 * h;
        let coeff = if i % 2 == 0 { 2.0 } else { 4.0 };
        sum += coeff * eval_at(x, env)?;
    }

    env.remove(var);

    Ok(MathValue::Float(sum * h / 3.0))
}

// ==========================================================================
// Helper math functions
// ==========================================================================

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn factorial(n: u64) -> u64 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

fn binomial(n: u64, k: u64) -> u64 {
    if k > n { return 0; }
    if k == 0 || k == n { return 1; }
    let k = if k > n - k { n - k } else { k };
    let mut result: u64 = 1;
    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }
    result
}

fn gamma(x: f64) -> f64 {
    if x <= 0.0 { return f64::NAN; }
    if x.fract() == 0.0 && x <= 21.0 {
        return factorial((x - 1.0) as u64) as f64;
    }
    let sqrt_2_pi = (2.0 * std::f64::consts::PI).sqrt();
    sqrt_2_pi * (x / std::f64::consts::E).powf(x) / x.sqrt()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_int() {
        let expr = MathExpr::Int(42);
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_eval_add() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(1)), Box::new(MathExpr::Int(2)));
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(3));
    }

    #[test]
    fn test_eval_mul() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(12));
    }

    #[test]
    fn test_eval_pow() {
        let expr = MathExpr::Pow(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        if let Value::Float(f) = evaluate(&expr).unwrap() {
            assert!((f - 8.0).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_eval_sqrt() {
        let expr = MathExpr::App("sqrt".to_string(), vec![MathExpr::Int(16)]);
        if let Value::Float(f) = evaluate(&expr).unwrap() {
            assert!((f - 4.0).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_eval_frac() {
        let expr = MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)]);
        if let Value::Float(f) = evaluate(&expr).unwrap() {
            assert!((f - 0.5).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_eval_pi() {
        let expr = MathExpr::Var("pi".to_string());
        if let Value::Float(f) = evaluate(&expr).unwrap() {
            assert!((f - std::f64::consts::PI).abs() < 0.0001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_eval_sum() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Int(3))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(6));
    }

    #[test]
    fn test_eval_prod() {
        let expr = MathExpr::Prod {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Int(4))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(24));
    }

    #[test]
    fn test_eval_factorial() {
        let expr = MathExpr::App("factorial".to_string(), vec![MathExpr::Int(5)]);
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(120));
    }

    #[test]
    fn test_eval_gcd() {
        let expr = MathExpr::App("gcd".to_string(), vec![MathExpr::Int(12), MathExpr::Int(8)]);
        let result = evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(4));
    }

    #[test]
    fn test_eval_array() {
        let expr = MathExpr::Array(vec![MathExpr::Int(1), MathExpr::Int(2), MathExpr::Int(3)]);
        let result = evaluate(&expr).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.len(), 3);
        } else {
            panic!("expected array");
        }
    }

    #[test]
    fn test_eval_zeros() {
        let expr = MathExpr::App("zeros".to_string(), vec![MathExpr::Int(3)]);
        let result = evaluate(&expr).unwrap();
        if let Value::Array(arr) = result {
            assert_eq!(arr.len(), 3);
            assert!(arr.iter().all(|v| matches!(v, Value::Float(f) if *f == 0.0)));
        } else {
            panic!("expected array");
        }
    }

    #[test]
    fn test_eval_matmul() {
        // 2x2 @ 2x2
        let a = MathExpr::Array(vec![
            MathExpr::Array(vec![MathExpr::Int(1), MathExpr::Int(2)]),
            MathExpr::Array(vec![MathExpr::Int(3), MathExpr::Int(4)]),
        ]);
        let b = MathExpr::Array(vec![
            MathExpr::Array(vec![MathExpr::Int(5), MathExpr::Int(6)]),
            MathExpr::Array(vec![MathExpr::Int(7), MathExpr::Int(8)]),
        ]);
        let expr = MathExpr::App("matmul".to_string(), vec![a, b]);
        let result = evaluate(&expr).unwrap();
        // Expected: [[19, 22], [43, 50]]
        if let Value::Array(outer) = result {
            assert_eq!(outer.len(), 2);
        } else {
            panic!("expected nested array");
        }
    }
}
