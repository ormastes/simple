//! Math expression evaluator.
//!
//! Evaluates math AST to numeric values. Supports:
//! - Basic arithmetic
//! - Trigonometric functions
//! - Logarithmic/exponential functions
//! - Special functions (factorial, binomial, etc.)
//! - Binders (sum, prod, int) with numeric evaluation

use super::ast::{get_constant, MathExpr, Range};
use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;

/// Evaluate math expression to a Value
pub fn evaluate(expr: &MathExpr) -> Result<Value, CompileError> {
    let mut env = HashMap::new();
    eval_with_env(expr, &mut env)
}

/// Evaluate with variable environment
fn eval_with_env(expr: &MathExpr, env: &mut HashMap<String, f64>) -> Result<Value, CompileError> {
    match expr {
        MathExpr::Int(n) => Ok(Value::Int(*n)),
        MathExpr::Float(f) => Ok(Value::Float(*f)),

        MathExpr::Var(name) => {
            // Check environment first
            if let Some(&val) = env.get(name) {
                return Ok(Value::Float(val));
            }
            // Then check built-in constants
            if let Some(val) = get_constant(name) {
                return Ok(Value::Float(val));
            }
            // Unknown variable - return as symbolic
            Err(CompileError::Semantic(format!(
                "undefined math variable: {}",
                name
            )))
        }

        MathExpr::Add(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(float_or_int(l + r))
        }

        MathExpr::Sub(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(float_or_int(l - r))
        }

        MathExpr::Mul(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(float_or_int(l * r))
        }

        MathExpr::Div(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            if r == 0.0 {
                return Err(CompileError::Semantic("division by zero".into()));
            }
            Ok(Value::Float(l / r))
        }

        MathExpr::Pow(base, exp) => {
            let b = eval_to_f64(base, env)?;
            let e = eval_to_f64(exp, env)?;
            Ok(Value::Float(b.powf(e)))
        }

        MathExpr::Mod(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            if r == 0.0 {
                return Err(CompileError::Semantic("modulo by zero".into()));
            }
            Ok(float_or_int(l % r))
        }

        MathExpr::Neg(inner) => {
            let val = eval_to_f64(inner, env)?;
            Ok(float_or_int(-val))
        }

        MathExpr::Abs(inner) => {
            let val = eval_to_f64(inner, env)?;
            Ok(float_or_int(val.abs()))
        }

        MathExpr::App(name, args) => eval_function(name, args, env),

        MathExpr::Subscript(base, _index) => {
            // For now, just evaluate the base
            // Full implementation would handle arrays/matrices
            eval_with_env(base, env)
        }

        MathExpr::Group(inner) => eval_with_env(inner, env),

        MathExpr::Sum { var, range, body } => eval_sum(var, range, body, env),

        MathExpr::Prod { var, range, body } => eval_prod(var, range, body, env),

        MathExpr::Integral { var, range, body } => eval_integral(var, range, body, env),

        // Comparisons return boolean (as 0.0 or 1.0)
        MathExpr::Eq(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool((l - r).abs() < 1e-10))
        }

        MathExpr::Neq(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool((l - r).abs() >= 1e-10))
        }

        MathExpr::Lt(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool(l < r))
        }

        MathExpr::Le(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool(l <= r))
        }

        MathExpr::Gt(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool(l > r))
        }

        MathExpr::Ge(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            Ok(Value::Bool(l >= r))
        }

        MathExpr::Approx(left, right) => {
            let l = eval_to_f64(left, env)?;
            let r = eval_to_f64(right, env)?;
            // Approximately equal within 1%
            let tolerance = (l.abs() + r.abs()) * 0.01;
            Ok(Value::Bool((l - r).abs() <= tolerance.max(1e-10)))
        }
    }
}

/// Evaluate expression to f64
fn eval_to_f64(expr: &MathExpr, env: &mut HashMap<String, f64>) -> Result<f64, CompileError> {
    match eval_with_env(expr, env)? {
        Value::Int(n) => Ok(n as f64),
        Value::Float(f) => Ok(f),
        Value::Bool(b) => Ok(if b { 1.0 } else { 0.0 }),
        other => Err(CompileError::Semantic(format!(
            "expected number, got {:?}",
            other
        ))),
    }
}

/// Convert f64 to Int or Float based on whether it's a whole number
fn float_or_int(val: f64) -> Value {
    if val.fract() == 0.0 && val.abs() < i64::MAX as f64 {
        Value::Int(val as i64)
    } else {
        Value::Float(val)
    }
}

/// Evaluate built-in function
fn eval_function(
    name: &str,
    args: &[MathExpr],
    env: &mut HashMap<String, f64>,
) -> Result<Value, CompileError> {
    match name {
        // === Basic Functions ===
        "sqrt" | "√" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x < 0.0 {
                return Err(CompileError::Semantic(
                    "cannot take sqrt of negative number".into(),
                ));
            }
            Ok(Value::Float(x.sqrt()))
        }

        "cbrt" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.cbrt()))
        }

        "root" => {
            require_args(name, args, 2)?;
            let n = eval_to_f64(&args[0], env)?;
            let x = eval_to_f64(&args[1], env)?;
            Ok(Value::Float(x.powf(1.0 / n)))
        }

        "abs" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(float_or_int(x.abs()))
        }

        "floor" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Int(x.floor() as i64))
        }

        "ceil" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Int(x.ceil() as i64))
        }

        "round" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Int(x.round() as i64))
        }

        "trunc" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Int(x.trunc() as i64))
        }

        "sign" | "sgn" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Int(if x > 0.0 {
                1
            } else if x < 0.0 {
                -1
            } else {
                0
            }))
        }

        // === Trigonometric ===
        "sin" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.sin()))
        }

        "cos" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.cos()))
        }

        "tan" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.tan()))
        }

        "asin" | "arcsin" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x < -1.0 || x > 1.0 {
                return Err(CompileError::Semantic("asin argument out of range".into()));
            }
            Ok(Value::Float(x.asin()))
        }

        "acos" | "arccos" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x < -1.0 || x > 1.0 {
                return Err(CompileError::Semantic("acos argument out of range".into()));
            }
            Ok(Value::Float(x.acos()))
        }

        "atan" | "arctan" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.atan()))
        }

        "atan2" => {
            require_args(name, args, 2)?;
            let y = eval_to_f64(&args[0], env)?;
            let x = eval_to_f64(&args[1], env)?;
            Ok(Value::Float(y.atan2(x)))
        }

        "sinh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.sinh()))
        }

        "cosh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.cosh()))
        }

        "tanh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.tanh()))
        }

        "asinh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.asinh()))
        }

        "acosh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.acosh()))
        }

        "atanh" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.atanh()))
        }

        // === Exponential/Logarithmic ===
        "exp" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            Ok(Value::Float(x.exp()))
        }

        "log" | "ln" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x <= 0.0 {
                return Err(CompileError::Semantic("log of non-positive number".into()));
            }
            Ok(Value::Float(x.ln()))
        }

        "log10" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x <= 0.0 {
                return Err(CompileError::Semantic("log of non-positive number".into()));
            }
            Ok(Value::Float(x.log10()))
        }

        "log2" => {
            require_args(name, args, 1)?;
            let x = eval_to_f64(&args[0], env)?;
            if x <= 0.0 {
                return Err(CompileError::Semantic("log of non-positive number".into()));
            }
            Ok(Value::Float(x.log2()))
        }

        // === Special Functions ===
        "frac" => {
            require_args(name, args, 2)?;
            let num = eval_to_f64(&args[0], env)?;
            let denom = eval_to_f64(&args[1], env)?;
            if denom == 0.0 {
                return Err(CompileError::Semantic("division by zero".into()));
            }
            Ok(Value::Float(num / denom))
        }

        "min" => {
            if args.is_empty() {
                return Err(CompileError::Semantic("min requires at least 1 argument".into()));
            }
            let mut result = eval_to_f64(&args[0], env)?;
            for arg in &args[1..] {
                let val = eval_to_f64(arg, env)?;
                if val < result {
                    result = val;
                }
            }
            Ok(float_or_int(result))
        }

        "max" => {
            if args.is_empty() {
                return Err(CompileError::Semantic("max requires at least 1 argument".into()));
            }
            let mut result = eval_to_f64(&args[0], env)?;
            for arg in &args[1..] {
                let val = eval_to_f64(arg, env)?;
                if val > result {
                    result = val;
                }
            }
            Ok(float_or_int(result))
        }

        "gcd" => {
            require_args(name, args, 2)?;
            let a = eval_to_f64(&args[0], env)? as i64;
            let b = eval_to_f64(&args[1], env)? as i64;
            Ok(Value::Int(gcd(a.abs(), b.abs())))
        }

        "lcm" => {
            require_args(name, args, 2)?;
            let a = eval_to_f64(&args[0], env)? as i64;
            let b = eval_to_f64(&args[1], env)? as i64;
            if a == 0 || b == 0 {
                return Ok(Value::Int(0));
            }
            Ok(Value::Int((a.abs() / gcd(a.abs(), b.abs())) * b.abs()))
        }

        "factorial" | "fact" => {
            require_args(name, args, 1)?;
            let n = eval_to_f64(&args[0], env)? as i64;
            if n < 0 {
                return Err(CompileError::Semantic(
                    "factorial of negative number".into(),
                ));
            }
            if n > 20 {
                // Use gamma function approximation for large values
                Ok(Value::Float(gamma(n as f64 + 1.0)))
            } else {
                Ok(Value::Int(factorial(n as u64) as i64))
            }
        }

        "binomial" | "binom" => {
            require_args(name, args, 2)?;
            let n = eval_to_f64(&args[0], env)? as i64;
            let k = eval_to_f64(&args[1], env)? as i64;
            if k < 0 || k > n {
                return Ok(Value::Int(0));
            }
            Ok(Value::Int(binomial(n as u64, k as u64) as i64))
        }

        _ => Err(CompileError::Semantic(format!(
            "unknown math function: {}",
            name
        ))),
    }
}

fn require_args(name: &str, args: &[MathExpr], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        Err(CompileError::Semantic(format!(
            "{} requires {} argument(s), got {}",
            name,
            expected,
            args.len()
        )))
    } else {
        Ok(())
    }
}

/// Evaluate summation: sum(i, a..b) body
fn eval_sum(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, f64>,
) -> Result<Value, CompileError> {
    let start = eval_to_f64(&range.start, env)? as i64;
    let end = eval_to_f64(&range.end, env)? as i64;

    let mut total = 0.0;
    for i in start..=end {
        env.insert(var.to_string(), i as f64);
        total += eval_to_f64(body, env)?;
    }
    env.remove(var);

    Ok(float_or_int(total))
}

/// Evaluate product: prod(i, a..b) body
fn eval_prod(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, f64>,
) -> Result<Value, CompileError> {
    let start = eval_to_f64(&range.start, env)? as i64;
    let end = eval_to_f64(&range.end, env)? as i64;

    let mut product = 1.0;
    for i in start..=end {
        env.insert(var.to_string(), i as f64);
        product *= eval_to_f64(body, env)?;
    }
    env.remove(var);

    Ok(float_or_int(product))
}

/// Evaluate integral using Simpson's rule
fn eval_integral(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, f64>,
) -> Result<Value, CompileError> {
    let a = eval_to_f64(&range.start, env)?;
    let b = eval_to_f64(&range.end, env)?;

    // Simpson's rule with 1000 intervals
    let n = 1000;
    let h = (b - a) / n as f64;

    // Helper to evaluate at a point
    let eval_at = |x: f64, env: &mut HashMap<String, f64>| -> Result<f64, CompileError> {
        env.insert(var.to_string(), x);
        eval_to_f64(body, env)
    };

    let mut sum = eval_at(a, env)? + eval_at(b, env)?;

    for i in 1..n {
        let x = a + i as f64 * h;
        let coeff = if i % 2 == 0 { 2.0 } else { 4.0 };
        sum += coeff * eval_at(x, env)?;
    }

    env.remove(var);

    Ok(Value::Float(sum * h / 3.0))
}

/// Greatest common divisor
fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// Factorial for small values
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// Binomial coefficient
fn binomial(n: u64, k: u64) -> u64 {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    // Use symmetry for efficiency
    let k = if k > n - k { n - k } else { k };
    let mut result: u64 = 1;
    for i in 0..k {
        result = result * (n - i) / (i + 1);
    }
    result
}

/// Gamma function approximation (Stirling's approximation)
fn gamma(x: f64) -> f64 {
    if x <= 0.0 {
        return f64::NAN;
    }
    // For integers, use factorial
    if x.fract() == 0.0 && x <= 21.0 {
        return factorial((x - 1.0) as u64) as f64;
    }
    // Stirling's approximation
    let sqrt_2_pi = (2.0 * std::f64::consts::PI).sqrt();
    sqrt_2_pi * (x / std::f64::consts::E).powf(x) / x.sqrt()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_int() {
        let expr = MathExpr::Int(42);
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(42));
    }

    #[test]
    fn test_eval_add() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(1)), Box::new(MathExpr::Int(2)));
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(3));
    }

    #[test]
    fn test_eval_mul() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(3)), Box::new(MathExpr::Int(4)));
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(12));
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
        // sum(i, 1..3) i = 1 + 2 + 3 = 6
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Int(3))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(6));
    }

    #[test]
    fn test_eval_prod() {
        // prod(i, 1..4) i = 1 * 2 * 3 * 4 = 24
        let expr = MathExpr::Prod {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Int(4))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(24));
    }

    #[test]
    fn test_eval_factorial() {
        let expr = MathExpr::App("factorial".to_string(), vec![MathExpr::Int(5)]);
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(120));
    }

    #[test]
    fn test_eval_gcd() {
        let expr = MathExpr::App("gcd".to_string(), vec![MathExpr::Int(12), MathExpr::Int(8)]);
        assert_eq!(evaluate(&expr).unwrap(), Value::Int(4));
    }
}
