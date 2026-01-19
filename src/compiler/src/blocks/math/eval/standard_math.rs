//! Standard mathematical functions.
//!
//! Provides:
//! - Trigonometric functions (sin, cos, tan, etc.)
//! - Logarithmic/exponential functions (log, exp, etc.)
//! - Special functions (factorial, binomial, gamma, gcd, lcm)
//! - Rounding functions (floor, ceil, round, trunc)
//! - Multi-arg functions (min, max, frac, root, atan2)

use super::super::tensor::Tensor;
use super::MathValue;
use crate::error::CompileError;

/// Helper for unary math functions (works on scalars and tensors)
pub fn unary_math_fn<F>(args: &[MathValue], op: F) -> Result<MathValue, CompileError>
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

// ==========================================================================
// Square Root and Power Functions
// ==========================================================================

pub fn eval_sqrt(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("sqrt requires 1 argument".into()));
    }
    match &args[0] {
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

pub fn eval_cbrt(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.cbrt())
}

// ==========================================================================
// Rounding Functions
// ==========================================================================

pub fn eval_abs(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.abs())
}

pub fn eval_floor(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.floor())
}

pub fn eval_ceil(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.ceil())
}

pub fn eval_round(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.round())
}

pub fn eval_trunc(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.trunc())
}

pub fn eval_sign(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.signum())
}

// ==========================================================================
// Exponential and Logarithmic Functions
// ==========================================================================

pub fn eval_exp(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.exp())
}

pub fn eval_log(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.ln())
}

pub fn eval_log10(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.log10())
}

pub fn eval_log2(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.log2())
}

// ==========================================================================
// Trigonometric Functions
// ==========================================================================

pub fn eval_sin(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.sin())
}

pub fn eval_cos(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.cos())
}

pub fn eval_tan(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.tan())
}

pub fn eval_asin(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.asin())
}

pub fn eval_acos(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.acos())
}

pub fn eval_atan(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.atan())
}

// ==========================================================================
// Hyperbolic Functions
// ==========================================================================

pub fn eval_sinh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.sinh())
}

pub fn eval_cosh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.cosh())
}

pub fn eval_asinh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.asinh())
}

pub fn eval_acosh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.acosh())
}

pub fn eval_atanh(args: &[MathValue]) -> Result<MathValue, CompileError> {
    unary_math_fn(args, |x| x.atanh())
}

// ==========================================================================
// Multi-Argument Functions
// ==========================================================================

pub fn eval_frac(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("frac requires 2 arguments".into()));
    }
    let num = args[0].as_f64()?;
    let denom = args[1].as_f64()?;
    if denom == 0.0 {
        return Err(CompileError::Semantic("division by zero".into()));
    }
    Ok(MathValue::Float(num / denom))
}

pub fn eval_root(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("root requires 2 arguments".into()));
    }
    let n = args[0].as_f64()?;
    let x = args[1].as_f64()?;
    Ok(MathValue::Float(x.powf(1.0 / n)))
}

pub fn eval_min(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.is_empty() {
        return Err(CompileError::Semantic("min requires at least 1 argument".into()));
    }
    if args.len() == 1 && args[0].is_tensor() {
        let t = get_tensor(&args[0])?;
        return Ok(MathValue::Float(t.min()));
    }
    let vals: Vec<f64> = args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
    Ok(MathValue::Float(vals.into_iter().fold(f64::INFINITY, f64::min)))
}

pub fn eval_max(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.is_empty() {
        return Err(CompileError::Semantic("max requires at least 1 argument".into()));
    }
    if args.len() == 1 && args[0].is_tensor() {
        let t = get_tensor(&args[0])?;
        return Ok(MathValue::Float(t.max()));
    }
    let vals: Vec<f64> = args.iter().map(|a| a.as_f64()).collect::<Result<_, _>>()?;
    Ok(MathValue::Float(vals.into_iter().fold(f64::NEG_INFINITY, f64::max)))
}

pub fn eval_atan2(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("atan2 requires 2 arguments".into()));
    }
    let y = args[0].as_f64()?;
    let x = args[1].as_f64()?;
    Ok(MathValue::Float(y.atan2(x)))
}

// ==========================================================================
// Number Theory Functions
// ==========================================================================

pub fn eval_gcd(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("gcd requires 2 arguments".into()));
    }
    let a = args[0].as_f64()? as i64;
    let b = args[1].as_f64()? as i64;
    Ok(MathValue::Int(gcd(a.abs(), b.abs())))
}

pub fn eval_lcm(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("lcm requires 2 arguments".into()));
    }
    let a = args[0].as_f64()? as i64;
    let b = args[1].as_f64()? as i64;
    if a == 0 || b == 0 {
        return Ok(MathValue::Int(0));
    }
    Ok(MathValue::Int((a.abs() / gcd(a.abs(), b.abs())) * b.abs()))
}

pub fn eval_factorial(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::Semantic("factorial requires 1 argument".into()));
    }
    let n = args[0].as_f64()? as i64;
    if n < 0 {
        return Err(CompileError::Semantic("factorial of negative".into()));
    }
    if n > 20 {
        Ok(MathValue::Float(gamma(n as f64 + 1.0)))
    } else {
        Ok(MathValue::Int(factorial(n as u64) as i64))
    }
}

pub fn eval_binomial(args: &[MathValue]) -> Result<MathValue, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::Semantic("binomial requires 2 arguments".into()));
    }
    let n = args[0].as_f64()? as i64;
    let k = args[1].as_f64()? as i64;
    if k < 0 || k > n {
        return Ok(MathValue::Int(0));
    }
    Ok(MathValue::Int(binomial(n as u64, k as u64) as i64))
}

// ==========================================================================
// Helper Functions
// ==========================================================================

fn get_tensor(val: &MathValue) -> Result<Tensor, CompileError> {
    match val {
        MathValue::Tensor(t) => Ok(t.clone()),
        v => Ok(Tensor::scalar(v.as_f64()?)),
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn binomial(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    let k = if k > n - k { n - k } else { k };
    let mut result: u64 = 1;
    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }
    result
}

fn gamma(x: f64) -> f64 {
    if x <= 0.0 {
        return f64::NAN;
    }
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
    fn test_sqrt() {
        let result = eval_sqrt(&[MathValue::Float(16.0)]).unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 4.0).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_sin() {
        let result = eval_sin(&[MathValue::Float(0.0)]).unwrap();
        match result {
            MathValue::Float(f) => assert!(f.abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_gcd() {
        let result = eval_gcd(&[MathValue::Int(12), MathValue::Int(8)]).unwrap();
        assert!(matches!(result, MathValue::Int(4)));
    }

    #[test]
    fn test_factorial() {
        let result = eval_factorial(&[MathValue::Int(5)]).unwrap();
        assert!(matches!(result, MathValue::Int(120)));
    }

    #[test]
    fn test_binomial() {
        let result = eval_binomial(&[MathValue::Int(5), MathValue::Int(2)]).unwrap();
        assert!(matches!(result, MathValue::Int(10)));
    }

    #[test]
    fn test_min() {
        let result = eval_min(&[MathValue::Int(3), MathValue::Int(1), MathValue::Int(4)]).unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 1.0).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }

    #[test]
    fn test_max() {
        let result = eval_max(&[MathValue::Int(3), MathValue::Int(1), MathValue::Int(4)]).unwrap();
        match result {
            MathValue::Float(f) => assert!((f - 4.0).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }
}
