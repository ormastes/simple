//! Math block handler for mathematical expressions.
//!
//! Supports Simple-compatible syntax (preferred) and LaTeX aliases (compatibility):
//!
//! ## Simple Syntax (Preferred)
//! - Functions: `sqrt(x)`, `frac(a, b)`, `sin(x)`, `cos(x)`
//! - Greek letters: `alpha`, `beta`, `pi`, `tau`
//! - Operators: `+`, `-`, `*`, `/`, `^`, `±`
//! - Subscripts: `x[i]`, `a[n+1]`
//! - Binders: `sum(i, 1..n) expr`, `int(x, 0..1) expr dx`
//! - Unicode: `√`, `α`, `β`, `π`, `∑`, `∫`
//!
//! ## LaTeX Compatibility (warns, normalized to Simple)
//! - `\frac{a}{b}` → `frac(a, b)`
//! - `\sqrt{x}` → `sqrt(x)`
//! - `\alpha` → `alpha`
//! - `\sum_{i=1}^{n}` → `sum(i, 1..n)`

mod lexer;
mod parser;
mod eval;
mod ast;

pub use self::ast::MathExpr;
use super::{BlockHandler, BlockResult};
use crate::error::CompileError;
use crate::value::Value;

/// Math block handler
pub struct MathBlock;

impl BlockHandler for MathBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse the math expression using the new parser
        let (expr, warnings) = parser::parse_math(payload)?;

        // Emit warnings for LaTeX compatibility syntax
        for warning in &warnings {
            eprintln!("warning: {}", warning);
        }

        // Evaluate the expression
        let result = eval::evaluate(&expr)?;

        // Return as a Block value
        Ok(Value::Block {
            kind: "m".to_string(),
            payload: payload.to_string(),
            result: Some(Box::new(result)),
        })
    }

    fn kind(&self) -> &'static str {
        "m"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_integer() {
        let handler = MathBlock;
        let result = handler.evaluate("42").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            assert_eq!(*r, Value::Int(42));
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_simple_addition() {
        let handler = MathBlock;
        let result = handler.evaluate("1 + 2").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            assert_eq!(*r, Value::Int(3));
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_pi_constant() {
        let handler = MathBlock;
        let result = handler.evaluate("pi").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - std::f64::consts::PI).abs() < 0.0001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_sqrt_function() {
        let handler = MathBlock;
        let result = handler.evaluate("sqrt(16)").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - 4.0).abs() < 0.001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_frac_function() {
        let handler = MathBlock;
        let result = handler.evaluate("frac(1, 2)").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - 0.5).abs() < 0.001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_latex_compat_frac() {
        let handler = MathBlock;
        // Should work but emit warning
        let result = handler.evaluate("\\frac{1}{2}").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - 0.5).abs() < 0.001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_latex_compat_sqrt() {
        let handler = MathBlock;
        let result = handler.evaluate("\\sqrt{16}").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - 4.0).abs() < 0.001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_implicit_multiplication() {
        let handler = MathBlock;
        let result = handler.evaluate("2 * 3").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            assert_eq!(*r, Value::Int(6));
        } else {
            panic!("expected block with result");
        }
    }

    #[test]
    fn test_power_operator() {
        let handler = MathBlock;
        let result = handler.evaluate("2^3").unwrap();
        if let Value::Block { result: Some(r), .. } = result {
            if let Value::Float(f) = *r {
                assert!((f - 8.0).abs() < 0.001);
            } else {
                panic!("expected float");
            }
        } else {
            panic!("expected block with result");
        }
    }
}
