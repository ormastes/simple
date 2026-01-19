//! Core binary and unary operations with type conversions.
//!
//! Handles arithmetic operations on MathValue types (Int, Float, Bool, Tensor)
//! with automatic type promotion and tensor broadcasting.

use super::super::tensor::Tensor;
use super::tensor_broadcasting::broadcast_tensor_op;
use super::MathValue;
use crate::error::CompileError;

/// Apply binary operation with broadcasting and type conversions
///
/// Handles:
/// - Scalar operations (Int + Int, Float + Float, Int + Float, etc.)
/// - Tensor operations with NumPy-style broadcasting
/// - Scalar-tensor operations (broadcast scalar to tensor shape)
/// - Bool to numeric conversions (true = 1.0, false = 0.0)
pub fn binary_op<F>(left: &MathValue, right: &MathValue, op: F, _name: &str) -> Result<MathValue, CompileError>
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

/// Apply unary operation to MathValue
///
/// Supports:
/// - Scalars: applies operation directly
/// - Tensors: applies operation element-wise
/// - Bool: converts to numeric first (true = 1.0, false = 0.0)
pub fn unary_op<F>(val: &MathValue, op: F) -> Result<MathValue, CompileError>
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
///
/// This preserves integer semantics when operations on integers
/// produce whole number results, avoiding unnecessary Float conversion.
///
/// # Examples
/// ```text
/// float_or_int_math(3.0)   → MathValue::Int(3)
/// float_or_int_math(3.14)  → MathValue::Float(3.14)
/// float_or_int_math(1e20)  → MathValue::Float(1e20)  // Too large for i64
/// ```
pub fn float_or_int_math(val: f64) -> MathValue {
    if val.fract() == 0.0 && val.abs() < i64::MAX as f64 {
        MathValue::Int(val as i64)
    } else {
        MathValue::Float(val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_op_int_int() {
        let result = binary_op(&MathValue::Int(3), &MathValue::Int(4), |a, b| a + b, "add").unwrap();
        assert!(matches!(result, MathValue::Int(7)));
    }

    #[test]
    fn test_binary_op_int_float() {
        let result = binary_op(&MathValue::Int(3), &MathValue::Float(4.5), |a, b| a + b, "add").unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 7.5).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_unary_op_int() {
        let result = unary_op(&MathValue::Int(5), |x| -x).unwrap();
        assert!(matches!(result, MathValue::Int(-5)));
    }

    #[test]
    fn test_unary_op_float() {
        let result = unary_op(&MathValue::Float(3.14), |x| x * 2.0).unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 6.28).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_float_or_int_whole() {
        let result = float_or_int_math(42.0);
        assert!(matches!(result, MathValue::Int(42)));
    }

    #[test]
    fn test_float_or_int_fractional() {
        let result = float_or_int_math(3.14);
        assert!(matches!(result, MathValue::Float(_)));
    }

    #[test]
    fn test_bool_conversion() {
        let result = binary_op(&MathValue::Bool(true), &MathValue::Int(5), |a, b| a + b, "add").unwrap();
        assert!(matches!(result, MathValue::Float(f) if (f - 6.0).abs() < 0.001));
    }
}
