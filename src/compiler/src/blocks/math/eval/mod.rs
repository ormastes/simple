//! Math expression evaluator - modular organization.
//!
//! This module provides comprehensive math evaluation supporting:
//! - Scalars (Int, Float, Bool)
//! - Tensors with NumPy-style broadcasting
//! - Standard math functions
//! - Tensor operations
//! - Binders (sum, prod, integral)
//!
//! ## Module Organization
//!
//! - **tensor_broadcasting**: Tensor conversion and NumPy-style broadcasting
//! - **core_ops**: Binary/unary operations with type conversions
//! - **binders**: Sum, product, and integral evaluation
//! - **standard_math**: Math functions (trig, log, special functions)
//! - **tensor_functions**: Tensor creation, manipulation, and reductions

use super::ast::{get_constant, MathExpr, Range};
use super::tensor::Tensor;
use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;

// Submodules
pub mod tensor_broadcasting;
pub mod core_ops;
pub mod binders;
pub mod standard_math;
pub mod tensor_functions;

// Re-export key items
pub use tensor_broadcasting::{broadcast_index, broadcast_shapes, broadcast_tensor_op, flatten_to_tensor, tensor_to_value};
pub use core_ops::{binary_op, float_or_int_math, unary_op};
pub use binders::{eval_integral, eval_prod, eval_sum};
pub use standard_math::unary_math_fn;
pub use tensor_functions::{args_to_shape, get_tensor, require_tensor_args};

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
            Err(CompileError::Semantic(format!("undefined math variable: {}", name)))
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
                (MathValue::Tensor(a), MathValue::Tensor(b)) => Ok(MathValue::Tensor(a.pow(b)?)),
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

/// Evaluate built-in function
fn eval_function(
    name: &str,
    args: &[MathExpr],
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    // Evaluate all arguments first
    let eval_args: Vec<MathValue> = args.iter().map(|a| eval_with_env(a, env)).collect::<Result<_, _>>()?;

    match name {
        // ==========================================================================
        // Tensor creation functions
        // ==========================================================================
        "tensor" => tensor_functions::eval_tensor(&eval_args),
        "zeros" => tensor_functions::eval_zeros(&eval_args),
        "ones" => tensor_functions::eval_ones(&eval_args),
        "full" => tensor_functions::eval_full(&eval_args),
        "eye" => tensor_functions::eval_eye(&eval_args),
        "arange" => tensor_functions::eval_arange(&eval_args),
        "linspace" => tensor_functions::eval_linspace(&eval_args),
        "rand" => tensor_functions::eval_rand(&eval_args),
        "randn" => tensor_functions::eval_randn(&eval_args),

        // ==========================================================================
        // Tensor operations
        // ==========================================================================
        "matmul" => tensor_functions::eval_matmul(&eval_args),
        "dot" => tensor_functions::eval_dot(&eval_args),
        "transpose" | "T" => tensor_functions::eval_transpose(&eval_args),
        "reshape" => tensor_functions::eval_reshape(&eval_args),
        "flatten" => tensor_functions::eval_flatten(&eval_args),
        "squeeze" => tensor_functions::eval_squeeze(&eval_args),
        "unsqueeze" => tensor_functions::eval_unsqueeze(&eval_args),

        // ==========================================================================
        // Tensor properties
        // ==========================================================================
        "shape" => tensor_functions::eval_shape(&eval_args),
        "ndim" => tensor_functions::eval_ndim(&eval_args),
        "numel" => tensor_functions::eval_numel(&eval_args),
        "item" => tensor_functions::eval_item(&eval_args),

        // ==========================================================================
        // Tensor reductions
        // ==========================================================================
        "sum" if eval_args.len() == 1 && eval_args[0].is_tensor() => tensor_functions::eval_sum_tensor(&eval_args),
        "mean" => tensor_functions::eval_mean(&eval_args),
        "var" => tensor_functions::eval_var(&eval_args),
        "std" => tensor_functions::eval_std(&eval_args),
        "argmin" => tensor_functions::eval_argmin(&eval_args),
        "argmax" => tensor_functions::eval_argmax(&eval_args),

        // ==========================================================================
        // Activation functions (element-wise)
        // ==========================================================================
        "relu" => tensor_functions::eval_relu(&eval_args),
        "sigmoid" => tensor_functions::eval_sigmoid(&eval_args),
        "softmax" => tensor_functions::eval_softmax(&eval_args),
        "tanh" => tensor_functions::eval_tanh(&eval_args),

        // ==========================================================================
        // Standard math functions (scalar, work element-wise on tensors)
        // ==========================================================================
        "sqrt" | "√" => standard_math::eval_sqrt(&eval_args),
        "cbrt" => standard_math::eval_cbrt(&eval_args),
        "abs" => standard_math::eval_abs(&eval_args),
        "floor" => standard_math::eval_floor(&eval_args),
        "ceil" => standard_math::eval_ceil(&eval_args),
        "round" => standard_math::eval_round(&eval_args),
        "trunc" => standard_math::eval_trunc(&eval_args),
        "sign" | "sgn" => standard_math::eval_sign(&eval_args),
        "exp" => standard_math::eval_exp(&eval_args),
        "log" | "ln" => standard_math::eval_log(&eval_args),
        "log10" => standard_math::eval_log10(&eval_args),
        "log2" => standard_math::eval_log2(&eval_args),
        "sin" => standard_math::eval_sin(&eval_args),
        "cos" => standard_math::eval_cos(&eval_args),
        "tan" => standard_math::eval_tan(&eval_args),
        "asin" | "arcsin" => standard_math::eval_asin(&eval_args),
        "acos" | "arccos" => standard_math::eval_acos(&eval_args),
        "atan" | "arctan" => standard_math::eval_atan(&eval_args),
        "sinh" => standard_math::eval_sinh(&eval_args),
        "cosh" => standard_math::eval_cosh(&eval_args),
        "asinh" => standard_math::eval_asinh(&eval_args),
        "acosh" => standard_math::eval_acosh(&eval_args),
        "atanh" => standard_math::eval_atanh(&eval_args),

        // ==========================================================================
        // Multi-arg math functions
        // ==========================================================================
        "frac" => standard_math::eval_frac(&eval_args),
        "root" => standard_math::eval_root(&eval_args),
        "min" => standard_math::eval_min(&eval_args),
        "max" => standard_math::eval_max(&eval_args),
        "gcd" => standard_math::eval_gcd(&eval_args),
        "lcm" => standard_math::eval_lcm(&eval_args),
        "factorial" | "fact" => standard_math::eval_factorial(&eval_args),
        "binomial" | "binom" => standard_math::eval_binomial(&eval_args),
        "atan2" => standard_math::eval_atan2(&eval_args),

        _ => Err(CompileError::Semantic(format!("unknown math function: {}", name))),
    }
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
