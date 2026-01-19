//! Math extern functions
//!
//! Basic mathematical operations for integer values.

use crate::error::CompileError;
use crate::value::Value;

/// Absolute value of an integer
///
/// Callable from Simple as: `abs(n)`
pub fn abs(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("abs expects 1 argument".into()))?;
    match val {
        Value::Int(i) => Ok(Value::Int(i.abs())),
        _ => Err(CompileError::Semantic("abs expects integer".into())),
    }
}

/// Minimum of two integers
///
/// Callable from Simple as: `min(a, b)`
pub fn min(args: &[Value]) -> Result<Value, CompileError> {
    let a = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?
        .as_int()?;
    let b = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?
        .as_int()?;
    Ok(Value::Int(a.min(b)))
}

/// Maximum of two integers
///
/// Callable from Simple as: `max(a, b)`
pub fn max(args: &[Value]) -> Result<Value, CompileError> {
    let a = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?
        .as_int()?;
    let b = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?
        .as_int()?;
    Ok(Value::Int(a.max(b)))
}

/// Square root of an integer (returns integer result)
///
/// Callable from Simple as: `sqrt(n)`
pub fn sqrt(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("sqrt expects 1 argument".into()))?
        .as_int()?;
    Ok(Value::Int((val as f64).sqrt() as i64))
}

/// Floor function (no-op for integers)
///
/// Callable from Simple as: `floor(n)`
pub fn floor(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("floor expects 1 argument".into()))?
        .as_int()?;
    Ok(Value::Int(val))
}

/// Ceiling function (no-op for integers)
///
/// Callable from Simple as: `ceil(n)`
pub fn ceil(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("ceil expects 1 argument".into()))?
        .as_int()?;
    Ok(Value::Int(val))
}

/// Power function (base^exponent)
///
/// Callable from Simple as: `pow(base, exponent)`
pub fn pow(args: &[Value]) -> Result<Value, CompileError> {
    let base = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?
        .as_int()?;
    let exp = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?
        .as_int()?;
    Ok(Value::Int(base.pow(exp as u32)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abs() {
        assert_eq!(abs(&[Value::Int(42)]).unwrap(), Value::Int(42));
        assert_eq!(abs(&[Value::Int(-42)]).unwrap(), Value::Int(42));
    }

    #[test]
    fn test_min() {
        assert_eq!(min(&[Value::Int(10), Value::Int(20)]).unwrap(), Value::Int(10));
        assert_eq!(min(&[Value::Int(20), Value::Int(10)]).unwrap(), Value::Int(10));
    }

    #[test]
    fn test_max() {
        assert_eq!(max(&[Value::Int(10), Value::Int(20)]).unwrap(), Value::Int(20));
        assert_eq!(max(&[Value::Int(20), Value::Int(10)]).unwrap(), Value::Int(20));
    }

    #[test]
    fn test_sqrt() {
        assert_eq!(sqrt(&[Value::Int(16)]).unwrap(), Value::Int(4));
        assert_eq!(sqrt(&[Value::Int(25)]).unwrap(), Value::Int(5));
    }

    #[test]
    fn test_floor_ceil() {
        // For integers, floor and ceil are identity operations
        assert_eq!(floor(&[Value::Int(42)]).unwrap(), Value::Int(42));
        assert_eq!(ceil(&[Value::Int(42)]).unwrap(), Value::Int(42));
    }

    #[test]
    fn test_pow() {
        assert_eq!(pow(&[Value::Int(2), Value::Int(3)]).unwrap(), Value::Int(8));
        assert_eq!(pow(&[Value::Int(5), Value::Int(2)]).unwrap(), Value::Int(25));
    }
}
