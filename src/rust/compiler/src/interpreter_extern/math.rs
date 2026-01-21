//! Math extern functions
//!
//! Basic mathematical operations for integer and float values.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

// Import runtime FFI math functions
use simple_runtime::value::ffi::math::{
    rt_math_pow, rt_math_log, rt_math_log10, rt_math_log2, rt_math_exp,
    rt_math_sqrt, rt_math_cbrt,
    rt_math_sin, rt_math_cos, rt_math_tan,
    rt_math_asin, rt_math_acos, rt_math_atan, rt_math_atan2,
    rt_math_sinh, rt_math_cosh, rt_math_tanh,
    rt_math_floor, rt_math_ceil,
    rt_math_nan, rt_math_inf, rt_math_is_nan, rt_math_is_inf, rt_math_is_finite,
};

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

// ============================================================================
// Float Math FFI Wrappers
// ============================================================================

/// rt_math_pow - Power function for floats
pub fn rt_math_pow_fn(args: &[Value]) -> Result<Value, CompileError> {
    let base = args.get(0).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_pow expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    let exp = args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_pow expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_pow(base, exp)))
}

/// rt_math_log - Natural logarithm for floats
pub fn rt_math_log_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_log expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_log(x)))
}

/// rt_math_log10 - Base-10 logarithm for floats
pub fn rt_math_log10_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_log10 expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_log10(x)))
}

/// rt_math_log2 - Base-2 logarithm for floats
pub fn rt_math_log2_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_log2 expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_log2(x)))
}

/// rt_math_exp - Exponential function for floats
pub fn rt_math_exp_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_exp expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_exp(x)))
}

/// rt_math_sqrt - Square root for floats
pub fn rt_math_sqrt_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_sqrt expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_sqrt(x)))
}

/// rt_math_cbrt - Cube root for floats
pub fn rt_math_cbrt_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_cbrt expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_cbrt(x)))
}

/// rt_math_sin - Sine function for floats (radians)
pub fn rt_math_sin_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_sin expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_sin(x)))
}

/// rt_math_cos - Cosine function for floats (radians)
pub fn rt_math_cos_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_cos expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_cos(x)))
}

/// rt_math_tan - Tangent function for floats (radians)
pub fn rt_math_tan_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_tan expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_tan(x)))
}

/// rt_math_asin - Arc sine for floats
pub fn rt_math_asin_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_asin expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_asin(x)))
}

/// rt_math_acos - Arc cosine for floats
pub fn rt_math_acos_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_acos expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_acos(x)))
}

/// rt_math_atan - Arc tangent for floats
pub fn rt_math_atan_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_atan expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_atan(x)))
}

/// rt_math_atan2 - Two-argument arc tangent for floats
pub fn rt_math_atan2_fn(args: &[Value]) -> Result<Value, CompileError> {
    let y = args.get(0).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_atan2 expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    let x = args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_atan2 expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_atan2(y, x)))
}

/// rt_math_sinh - Hyperbolic sine for floats
pub fn rt_math_sinh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_sinh expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_sinh(x)))
}

/// rt_math_cosh - Hyperbolic cosine for floats
pub fn rt_math_cosh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_cosh expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_cosh(x)))
}

/// rt_math_tanh - Hyperbolic tangent for floats
pub fn rt_math_tanh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_tanh expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_tanh(x)))
}

/// rt_math_floor - Floor function for floats
pub fn rt_math_floor_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_floor expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_floor(x)))
}

/// rt_math_ceil - Ceiling function for floats
pub fn rt_math_ceil_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_ceil expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Float(rt_math_ceil(x)))
}

// ============================================================================
// Special Values
// ============================================================================

/// rt_math_nan - Returns IEEE 754 NaN
pub fn rt_math_nan_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Float(rt_math_nan()))
}

/// rt_math_inf - Returns IEEE 754 positive infinity
pub fn rt_math_inf_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Float(rt_math_inf()))
}

/// rt_math_is_nan - Check if value is NaN
pub fn rt_math_is_nan_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_is_nan expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Bool(rt_math_is_nan(x)))
}

/// rt_math_is_inf - Check if value is infinite
pub fn rt_math_is_inf_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_is_inf expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Bool(rt_math_is_inf(x)))
}

/// rt_math_is_finite - Check if value is finite
pub fn rt_math_is_finite_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_math_is_finite expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?.as_float()?;
    Ok(Value::Bool(rt_math_is_finite(x)))
}
