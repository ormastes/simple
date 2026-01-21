//! Mathematical binders: summation, product, and integration.
//!
//! Provides:
//! - Σ (sum): Discrete summation over a range
//! - Π (prod): Discrete product over a range
//! - ∫ (integral): Numerical integration using Simpson's rule

use super::super::ast::{MathExpr, Range};
use super::core_ops::float_or_int_math;
use super::MathValue;
use crate::error::CompileError;
use std::collections::HashMap;

/// Evaluate summation: Σ(i, a..b) body
///
/// Computes the sum of body(i) for i from a to b (inclusive).
///
/// # Examples
/// ```text
/// sum(i, 1..3) i     → 1 + 2 + 3 = 6
/// sum(i, 1..4) i²    → 1 + 4 + 9 + 16 = 30
/// sum(i, 0..n) 1     → n + 1  (count)
/// ```
pub fn eval_sum(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    // Import eval_with_env from parent module
    use super::super::super::super::blocks::math::eval::eval_with_env;

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

/// Evaluate product: Π(i, a..b) body
///
/// Computes the product of body(i) for i from a to b (inclusive).
///
/// # Examples
/// ```text
/// prod(i, 1..4) i    → 1 × 2 × 3 × 4 = 24 (factorial)
/// prod(i, 1..n) 2    → 2^n
/// prod(i, 2..4) i    → 2 × 3 × 4 = 24
/// ```
pub fn eval_prod(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    use super::super::super::super::blocks::math::eval::eval_with_env;

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

/// Evaluate integral using Simpson's rule: ∫(x, a..b) f(x)
///
/// Numerically integrates f(x) from a to b using Simpson's 1/3 rule
/// with 1000 subdivisions for reasonable accuracy.
///
/// # Simpson's Rule
/// ∫[a,b] f(x) dx ≈ (h/3) × [f(a) + 4f(x₁) + 2f(x₂) + 4f(x₃) + ... + f(b)]
///
/// where h = (b - a) / n and xᵢ are evenly spaced points.
///
/// # Examples
/// ```text
/// int(x, 0..1) x      → 0.5  (area under y = x from 0 to 1)
/// int(x, 0..π) sin(x) → 2.0  (area under sine wave)
/// int(x, 0..2) x²     → 8/3 ≈ 2.667
/// ```
pub fn eval_integral(
    var: &str,
    range: &Range,
    body: &MathExpr,
    env: &mut HashMap<String, MathValue>,
) -> Result<MathValue, CompileError> {
    use super::super::super::super::blocks::math::eval::eval_with_env;

    let a = eval_with_env(&range.start, env)?.as_f64()?;
    let b = eval_with_env(&range.end, env)?.as_f64()?;

    let n = 1000; // Number of subdivisions
    let h = (b - a) / n as f64;

    let eval_at = |x: f64, env: &mut HashMap<String, MathValue>| -> Result<f64, CompileError> {
        env.insert(var.to_string(), MathValue::Float(x));
        eval_with_env(body, env)?.as_f64()
    };

    // Simpson's rule: (h/3) × [f(a) + 4×Σ(odd i) + 2×Σ(even i) + f(b)]
    let mut sum = eval_at(a, env)? + eval_at(b, env)?;

    for i in 1..n {
        let x = a + i as f64 * h;
        let coeff = if i % 2 == 0 { 2.0 } else { 4.0 };
        sum += coeff * eval_at(x, env)?;
    }

    env.remove(var);

    Ok(MathValue::Float(sum * h / 3.0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::super::ast::Range;

    #[test]
    fn test_eval_sum_simple() {
        let mut env = HashMap::new();
        let range = Range::new(MathExpr::Int(1), MathExpr::Int(3));
        let body = MathExpr::Var("i".to_string());

        let result = eval_sum("i", &range, &body, &mut env).unwrap();
        // 1 + 2 + 3 = 6
        assert!(matches!(result, MathValue::Int(6)));
    }

    #[test]
    fn test_eval_prod_factorial() {
        let mut env = HashMap::new();
        let range = Range::new(MathExpr::Int(1), MathExpr::Int(4));
        let body = MathExpr::Var("i".to_string());

        let result = eval_prod("i", &range, &body, &mut env).unwrap();
        // 1 × 2 × 3 × 4 = 24
        assert!(matches!(result, MathValue::Int(24)));
    }

    #[test]
    fn test_eval_integral_linear() {
        let mut env = HashMap::new();
        let range = Range::new(MathExpr::Float(0.0), MathExpr::Float(1.0));
        let body = MathExpr::Var("x".to_string());

        let result = eval_integral("x", &range, &body, &mut env).unwrap();
        // ∫₀¹ x dx = 0.5
        match result {
            MathValue::Float(f) => assert!((f - 0.5).abs() < 0.001),
            _ => panic!("expected float"),
        }
    }
}
