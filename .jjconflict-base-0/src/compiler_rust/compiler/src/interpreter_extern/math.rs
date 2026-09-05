//! Math extern functions
//!
//! Basic mathematical operations for integer and float values.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

// Import runtime SFFI math functions
use simple_runtime::value::sffi::math::{
    rt_math_pow, rt_math_log, rt_math_log10, rt_math_log2, rt_math_exp, rt_math_sqrt, rt_math_cbrt, rt_math_sin,
    rt_math_cos, rt_math_tan, rt_math_asin, rt_math_acos, rt_math_atan, rt_math_atan2, rt_math_sinh, rt_math_cosh,
    rt_math_tanh, rt_math_floor, rt_math_ceil, rt_math_nan, rt_math_inf, rt_math_is_nan, rt_math_is_inf,
    rt_math_is_finite,
};

/// True when this value is floating point, so the numeric builtins below can
/// pick a float path instead of forcing everything through `as_int()`.
///
/// `as_int()` on a float TRUNCATES: it turned `min(1.5, 2.5)` into `1` in this
/// lane (the whole-module interpreter fallback), silently losing the fraction.
/// That was invisible for a long time because
/// `src/lib/nogc_sync_mut/runtime_wrappers.spl` accidentally SHADOWED these
/// builtins with pure-Simple reimplementations that happened to be
/// float-tolerant, so most callers never reached this code at all. Removing
/// those shadows reroutes callers here, which is why these paths had to become
/// float-correct first.
/// doc/08_tracking/bug/numeric_builtins_hardcode_i64_result_type_2026-08-10.md
fn is_float(v: &Value) -> bool {
    matches!(v, Value::Float(_) | Value::Float32(_))
}

/// Coerce to `f64` for the float path. Integers widen, which is what makes
/// mixed calls like `pow(2.0, 3)` evaluate as floats rather than erroring.
fn as_f64(v: &Value) -> Result<f64, CompileError> {
    match v {
        Value::Float(f) => Ok(*f),
        Value::Float32(f) => Ok(*f as f64),
        Value::Int(i) => Ok(*i as f64),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("expected a numeric argument");
            Err(CompileError::semantic_with_context("expected numeric".to_string(), ctx))
        }
    }
}

fn arg_at<'a>(args: &'a [Value], index: usize, name: &str, arity: usize) -> Result<&'a Value, CompileError> {
    args.get(index).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help(format!("{} expects exactly {} argument(s)", name, arity));
        CompileError::semantic_with_context(format!("{} expects {} argument(s)", name, arity), ctx)
    })
}

/// Absolute value
///
/// Callable from Simple as: `abs(n)`. Integer in, integer out; float in,
/// float out.
pub fn abs(args: &[Value]) -> Result<Value, CompileError> {
    let val = arg_at(args, 0, "abs", 1)?;
    match val {
        Value::Int(i) => Ok(Value::Int(i.abs())),
        v if is_float(v) => Ok(Value::Float(as_f64(v)?.abs())),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("abs expects a numeric argument");
            Err(CompileError::semantic_with_context(
                "abs expects a number".to_string(),
                ctx,
            ))
        }
    }
}

/// Minimum of two numbers
///
/// Callable from Simple as: `min(a, b)`. Float if either argument is float.
pub fn min(args: &[Value]) -> Result<Value, CompileError> {
    let a = arg_at(args, 0, "min", 2)?;
    let b = arg_at(args, 1, "min", 2)?;
    if is_float(a) || is_float(b) {
        return Ok(Value::Float(as_f64(a)?.min(as_f64(b)?)));
    }
    Ok(Value::Int(a.as_int()?.min(b.as_int()?)))
}

/// Maximum of two numbers
///
/// Callable from Simple as: `max(a, b)`. Float if either argument is float.
pub fn max(args: &[Value]) -> Result<Value, CompileError> {
    let a = arg_at(args, 0, "max", 2)?;
    let b = arg_at(args, 1, "max", 2)?;
    if is_float(a) || is_float(b) {
        return Ok(Value::Float(as_f64(a)?.max(as_f64(b)?)));
    }
    Ok(Value::Int(a.as_int()?.max(b.as_int()?)))
}

/// Square root
///
/// Callable from Simple as: `sqrt(n)`. A float argument returns a float
/// (`sqrt(16.0)` => `4.0`); an integer argument keeps the previous
/// truncating-to-integer behaviour so integer callers are unchanged.
pub fn sqrt(args: &[Value]) -> Result<Value, CompileError> {
    let val = arg_at(args, 0, "sqrt", 1)?;
    if is_float(val) {
        return Ok(Value::Float(as_f64(val)?.sqrt()));
    }
    Ok(Value::Int((val.as_int()? as f64).sqrt() as i64))
}

/// Floor
///
/// Callable from Simple as: `floor(n)`. Genuinely rounds down for floats
/// (`floor(1.7)` => `1.0`); a no-op for integers, as before.
pub fn floor(args: &[Value]) -> Result<Value, CompileError> {
    let val = arg_at(args, 0, "floor", 1)?;
    if is_float(val) {
        return Ok(Value::Float(as_f64(val)?.floor()));
    }
    Ok(Value::Int(val.as_int()?))
}

/// Ceiling
///
/// Callable from Simple as: `ceil(n)`. Genuinely rounds up for floats
/// (`ceil(1.2)` => `2.0`); a no-op for integers, as before.
pub fn ceil(args: &[Value]) -> Result<Value, CompileError> {
    let val = arg_at(args, 0, "ceil", 1)?;
    if is_float(val) {
        return Ok(Value::Float(as_f64(val)?.ceil()));
    }
    Ok(Value::Int(val.as_int()?))
}

/// Power function (base^exponent)
///
/// Callable from Simple as: `pow(base, exponent)`. Float if either argument is
/// float. The integer path additionally rejects a NEGATIVE exponent instead of
/// casting it to `u32`: `(exp as u32)` wrapped a negative exponent to a huge
/// unsigned value, and `i64::pow` then panicked or overflowed rather than
/// reporting anything useful.
pub fn pow(args: &[Value]) -> Result<Value, CompileError> {
    let base = arg_at(args, 0, "pow", 2)?;
    let exp = arg_at(args, 1, "pow", 2)?;
    if is_float(base) || is_float(exp) {
        return Ok(Value::Float(as_f64(base)?.powf(as_f64(exp)?)));
    }
    let b = base.as_int()?;
    let e = exp.as_int()?;
    if e < 0 {
        let ctx = ErrorContext::new()
            .with_code(codes::TYPE_MISMATCH)
            .with_help("use a float base for a negative exponent, e.g. pow(2.0, -3)");
        return Err(CompileError::semantic_with_context(
            "pow with a negative exponent requires a float base".to_string(),
            ctx,
        ));
    }
    Ok(Value::Int(b.saturating_pow(e.min(u32::MAX as i64) as u32)))
}

// ============================================================================
// Float Math SFFI Wrappers
// ============================================================================

/// rt_math_pow - Power function for floats
pub fn rt_math_pow_fn(args: &[Value]) -> Result<Value, CompileError> {
    let base = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_pow expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    let exp = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_pow expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_pow(base, exp)))
}

/// rt_math_log - Natural logarithm for floats
pub fn rt_math_log_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_log expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_log(x)))
}

/// rt_math_log10 - Base-10 logarithm for floats
pub fn rt_math_log10_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_log10 expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_log10(x)))
}

/// rt_math_log2 - Base-2 logarithm for floats
pub fn rt_math_log2_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_log2 expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_log2(x)))
}

/// rt_math_exp - Exponential function for floats
pub fn rt_math_exp_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_exp expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_exp(x)))
}

/// rt_math_sqrt - Square root for floats
pub fn rt_math_sqrt_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_sqrt expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_sqrt(x)))
}

/// rt_math_cbrt - Cube root for floats
pub fn rt_math_cbrt_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_cbrt expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_cbrt(x)))
}

/// rt_math_sin - Sine function for floats (radians)
pub fn rt_math_sin_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_sin expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_sin(x)))
}

/// rt_math_cos - Cosine function for floats (radians)
pub fn rt_math_cos_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_cos expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_cos(x)))
}

/// rt_math_tan - Tangent function for floats (radians)
pub fn rt_math_tan_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_tan expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_tan(x)))
}

/// rt_math_asin - Arc sine for floats
pub fn rt_math_asin_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_asin expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_asin(x)))
}

/// rt_math_acos - Arc cosine for floats
pub fn rt_math_acos_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_acos expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_acos(x)))
}

/// rt_math_atan - Arc tangent for floats
pub fn rt_math_atan_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_atan expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_atan(x)))
}

/// rt_math_atan2 - Two-argument arc tangent for floats
pub fn rt_math_atan2_fn(args: &[Value]) -> Result<Value, CompileError> {
    let y = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_atan2 expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    let x = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_atan2 expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_atan2(y, x)))
}

/// rt_math_sinh - Hyperbolic sine for floats
pub fn rt_math_sinh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_sinh expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_sinh(x)))
}

/// rt_math_cosh - Hyperbolic cosine for floats
pub fn rt_math_cosh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_cosh expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_cosh(x)))
}

/// rt_math_tanh - Hyperbolic tangent for floats
pub fn rt_math_tanh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_tanh expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_tanh(x)))
}

/// rt_math_floor - Floor function for floats
pub fn rt_math_floor_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_floor expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Float(rt_math_floor(x)))
}

/// rt_math_ceil - Ceiling function for floats
pub fn rt_math_ceil_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_ceil expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
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
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_is_nan expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Bool(rt_math_is_nan(x)))
}

/// rt_math_is_inf - Check if value is infinite
pub fn rt_math_is_inf_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_is_inf expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Bool(rt_math_is_inf(x)))
}

/// rt_math_is_finite - Check if value is finite
pub fn rt_math_is_finite_fn(args: &[Value]) -> Result<Value, CompileError> {
    let x = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_math_is_finite expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;
    Ok(Value::Bool(rt_math_is_finite(x)))
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
