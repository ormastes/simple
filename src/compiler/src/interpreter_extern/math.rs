//! Math extern functions
//!
//! Basic mathematical operations for integer values.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

/// Absolute value of an integer
///
/// Callable from Simple as: `abs(n)`
pub fn abs(args: &[Value]) -> Result<Value, CompileError> {
    let val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("abs expects exactly 1 argument");
        CompileError::semantic_with_context("abs expects 1 argument".to_string(), ctx)
    })?;
    match val {
        Value::Int(i) => Ok(Value::Int(i.abs())),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("abs expects an integer argument");
            Err(CompileError::semantic_with_context(
                "abs expects integer".to_string(),
                ctx,
            ))
        }
    }
}

/// Minimum of two integers
///
/// Callable from Simple as: `min(a, b)`
pub fn min(args: &[Value]) -> Result<Value, CompileError> {
    let a = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("min expects exactly 2 arguments");
            CompileError::semantic_with_context("min expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let b = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("min expects exactly 2 arguments");
            CompileError::semantic_with_context("min expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    Ok(Value::Int(a.min(b)))
}

/// Maximum of two integers
///
/// Callable from Simple as: `max(a, b)`
pub fn max(args: &[Value]) -> Result<Value, CompileError> {
    let a = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("max expects exactly 2 arguments");
            CompileError::semantic_with_context("max expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let b = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("max expects exactly 2 arguments");
            CompileError::semantic_with_context("max expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    Ok(Value::Int(a.max(b)))
}

/// Square root of an integer (returns integer result)
///
/// Callable from Simple as: `sqrt(n)`
pub fn sqrt(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("sqrt expects exactly 1 argument");
            CompileError::semantic_with_context("sqrt expects 1 argument".to_string(), ctx)
        })?
        .as_int()?;
    Ok(Value::Int((val as f64).sqrt() as i64))
}

/// Floor function (no-op for integers)
///
/// Callable from Simple as: `floor(n)`
pub fn floor(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("floor expects exactly 1 argument");
            CompileError::semantic_with_context("floor expects 1 argument".to_string(), ctx)
        })?
        .as_int()?;
    Ok(Value::Int(val))
}

/// Ceiling function (no-op for integers)
///
/// Callable from Simple as: `ceil(n)`
pub fn ceil(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("ceil expects exactly 1 argument");
            CompileError::semantic_with_context("ceil expects 1 argument".to_string(), ctx)
        })?
        .as_int()?;
    Ok(Value::Int(val))
}

/// Power function (base^exponent)
///
/// Callable from Simple as: `pow(base, exponent)`
pub fn pow(args: &[Value]) -> Result<Value, CompileError> {
    let base = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("pow expects exactly 2 arguments");
            CompileError::semantic_with_context("pow expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let exp = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("pow expects exactly 2 arguments");
            CompileError::semantic_with_context("pow expects 2 arguments".to_string(), ctx)
        })?
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
