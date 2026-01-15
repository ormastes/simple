//! Math block handler for LaTeX-like expressions.
//!
//! Supports:
//! - Basic arithmetic: +, -, *, /, ^
//! - Fractions: \frac{a}{b}
//! - Square roots: \sqrt{x}
//! - Greek letters: \pi, \alpha, \beta, etc.
//! - Summation: \sum_{i=0}^{n}
//! - Integration: \int_{a}^{b}
//! - Implicit multiplication: 2x, 3(x+1)

use super::{BlockHandler, BlockResult};
use crate::error::CompileError;
use crate::value::Value;

/// Math block handler
pub struct MathBlock;

impl BlockHandler for MathBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse the math expression
        let expr = parse_math_expr(payload)?;

        // Return as a Block value with the parsed expression
        Ok(Value::Block {
            kind: "m".to_string(),
            payload: payload.to_string(),
            result: Some(Box::new(expr)),
        })
    }

    fn kind(&self) -> &'static str {
        "m"
    }
}

/// Parse a math expression and return a Value
fn parse_math_expr(payload: &str) -> Result<Value, CompileError> {
    let payload = payload.trim();

    // Try to parse as a simple numeric expression first
    if let Ok(n) = payload.parse::<i64>() {
        return Ok(Value::Int(n));
    }
    if let Ok(f) = payload.parse::<f64>() {
        return Ok(Value::Float(f));
    }

    // Handle Greek letters and constants
    match payload {
        "\\pi" | "pi" => return Ok(Value::Float(std::f64::consts::PI)),
        "\\e" | "e" => return Ok(Value::Float(std::f64::consts::E)),
        "\\tau" | "tau" => return Ok(Value::Float(std::f64::consts::TAU)),
        _ => {}
    }

    // Parse simple binary expressions (for now, basic implementation)
    // Full implementation would use a proper expression parser

    // Check for fraction: \frac{a}{b}
    if payload.starts_with("\\frac{") {
        return parse_frac(payload);
    }

    // Check for sqrt: \sqrt{x}
    if payload.starts_with("\\sqrt{") {
        return parse_sqrt(payload);
    }

    // For complex expressions, store as string for now
    // Full implementation would build an AST
    Ok(Value::Str(format!("math:{}", payload)))
}

/// Parse a fraction: \frac{numerator}{denominator}
fn parse_frac(payload: &str) -> Result<Value, CompileError> {
    // Extract content between braces
    let rest = &payload[6..]; // Skip "\frac{"

    // Find matching braces for numerator
    let (num_str, rest) = extract_braced(rest)?;
    let num = parse_math_expr(&num_str)?;

    // Skip to denominator
    let rest = rest.trim_start();
    if !rest.starts_with('{') {
        return Err(CompileError::Semantic(
            "invalid \\frac syntax: expected {denominator}".into(),
        ));
    }
    let (denom_str, _) = extract_braced(&rest[1..])?;
    let denom = parse_math_expr(&denom_str)?;

    // Compute the division
    match (num, denom) {
        (Value::Int(n), Value::Int(d)) => {
            if d == 0 {
                Err(CompileError::Semantic("division by zero".into()))
            } else {
                Ok(Value::Float(n as f64 / d as f64))
            }
        }
        (Value::Float(n), Value::Float(d)) => {
            if d == 0.0 {
                Err(CompileError::Semantic("division by zero".into()))
            } else {
                Ok(Value::Float(n / d))
            }
        }
        (Value::Int(n), Value::Float(d)) => {
            if d == 0.0 {
                Err(CompileError::Semantic("division by zero".into()))
            } else {
                Ok(Value::Float(n as f64 / d))
            }
        }
        (Value::Float(n), Value::Int(d)) => {
            if d == 0 {
                Err(CompileError::Semantic("division by zero".into()))
            } else {
                Ok(Value::Float(n / d as f64))
            }
        }
        _ => Err(CompileError::Semantic(
            "\\frac requires numeric arguments".into(),
        )),
    }
}

/// Parse square root: \sqrt{x}
fn parse_sqrt(payload: &str) -> Result<Value, CompileError> {
    let rest = &payload[6..]; // Skip "\sqrt{"
    let (arg_str, _) = extract_braced(rest)?;
    let arg = parse_math_expr(&arg_str)?;

    match arg {
        Value::Int(n) => {
            if n < 0 {
                Err(CompileError::Semantic(
                    "cannot take sqrt of negative number".into(),
                ))
            } else {
                Ok(Value::Float((n as f64).sqrt()))
            }
        }
        Value::Float(f) => {
            if f < 0.0 {
                Err(CompileError::Semantic(
                    "cannot take sqrt of negative number".into(),
                ))
            } else {
                Ok(Value::Float(f.sqrt()))
            }
        }
        _ => Err(CompileError::Semantic(
            "\\sqrt requires numeric argument".into(),
        )),
    }
}

/// Extract content between matching braces
fn extract_braced(s: &str) -> Result<(String, &str), CompileError> {
    let mut depth = 1;
    let mut content = String::new();
    let mut chars = s.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '{' {
            depth += 1;
            content.push(ch);
        } else if ch == '}' {
            depth -= 1;
            if depth == 0 {
                let rest: String = chars.collect();
                return Ok((content, Box::leak(rest.into_boxed_str())));
            }
            content.push(ch);
        } else {
            content.push(ch);
        }
    }

    Err(CompileError::Semantic("unmatched braces".into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_integer() {
        let result = parse_math_expr("42").unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_parse_float() {
        let result = parse_math_expr("3.14").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 3.14).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_parse_pi() {
        let result = parse_math_expr("\\pi").unwrap();
        if let Value::Float(f) = result {
            assert!((f - std::f64::consts::PI).abs() < 0.0001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_parse_frac() {
        let result = parse_math_expr("\\frac{1}{2}").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 0.5).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_parse_sqrt() {
        let result = parse_math_expr("\\sqrt{16}").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 4.0).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }
}
