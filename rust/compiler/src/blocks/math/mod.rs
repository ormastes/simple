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
pub mod tensor;
pub mod rendering;
pub mod backend;

pub use self::ast::MathExpr;
pub use self::tensor::Tensor;
use super::{BlockHandler, BlockResult};
use crate::error::CompileError;
use crate::value::Value;

/// Parse math expression and export to LaTeX
pub fn to_latex(input: &str) -> Result<String, CompileError> {
    let (expr, _warnings) = parser::parse_math(input)?;
    Ok(expr.to_latex())
}

/// Parse math expression and export to MathML
pub fn to_mathml(input: &str) -> Result<String, CompileError> {
    let (expr, _warnings) = parser::parse_math(input)?;
    Ok(expr.to_mathml())
}

/// Parse math expression and export to Unicode text
pub fn to_text(input: &str) -> Result<String, CompileError> {
    let (expr, _warnings) = parser::parse_math(input)?;
    Ok(expr.to_text())
}

/// Parse math expression and export to Lean4 syntax
pub fn to_lean(input: &str) -> Result<String, CompileError> {
    let (expr, _warnings) = parser::parse_math(input)?;
    Ok(expr.to_lean())
}

/// Math block handler
pub struct MathBlock;

impl MathBlock {
    /// Evaluate with a specific preferred backend.
    pub fn evaluate_with_backend(
        &self,
        payload: &str,
        preferred: backend::MathBackend,
    ) -> BlockResult {
        let (expr, warnings) = parser::parse_math(payload)?;

        for warning in &warnings {
            eprintln!("warning: {}", warning);
        }

        eval::evaluate_with_backend(&expr, preferred)
    }
}

impl BlockHandler for MathBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse the math expression, checking for backend directive
        let (payload_expr, preferred) = parse_backend_directive(payload);

        let (expr, warnings) = parser::parse_math(payload_expr)?;

        // Emit warnings for LaTeX compatibility syntax
        for warning in &warnings {
            eprintln!("warning: {}", warning);
        }

        // Evaluate with backend selection
        eval::evaluate_with_backend(&expr, preferred)
    }

    fn kind(&self) -> &'static str {
        "m"
    }

    fn display_string(&self, payload: &str) -> String {
        let (payload_expr, _) = parse_backend_directive(payload);
        match parser::parse_math(payload_expr) {
            Ok((expr, _)) => rendering::unicode_text::to_text(&expr),
            Err(_) => format!("m{{{}}}", payload),
        }
    }
}

/// Parse an optional `use backend X` directive at the start of a math payload.
///
/// Returns the remaining expression string and the preferred backend.
/// If no directive is found, returns the original payload and `MathBackend::Auto`.
fn parse_backend_directive(payload: &str) -> (&str, backend::MathBackend) {
    let trimmed = payload.trim_start();
    if let Some(rest) = trimmed.strip_prefix("use backend ") {
        let rest = rest.trim_start();
        // Find the backend name (until whitespace or semicolon)
        let end = rest
            .find(|c: char| c.is_whitespace() || c == ';')
            .unwrap_or(rest.len());
        let (name, remainder) = rest.split_at(end);
        let remainder = remainder.trim_start_matches(';').trim_start();

        let backend = backend::MathBackend::from_str(name).unwrap_or_else(|| {
            eprintln!("warning: unknown backend '{}', using auto", name);
            backend::MathBackend::Auto
        });

        tracing::debug!(
            "[math::block] Parsed backend directive: use backend {} -> {:?}",
            name,
            backend
        );

        if remainder.is_empty() {
            // Directive only, no expression - this shouldn't happen in practice
            (payload, backend)
        } else {
            (remainder, backend)
        }
    } else {
        (payload, backend::MathBackend::Auto)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_integer() {
        let handler = MathBlock;
        let result = handler.evaluate("42").unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_simple_addition() {
        let handler = MathBlock;
        let result = handler.evaluate("1 + 2").unwrap();
        assert_eq!(result, Value::Int(3));
    }

    #[test]
    fn test_pi_constant() {
        let handler = MathBlock;
        let result = handler.evaluate("pi").unwrap();
        if let Value::Float(f) = result {
            assert!((f - std::f64::consts::PI).abs() < 0.0001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_sqrt_function() {
        let handler = MathBlock;
        let result = handler.evaluate("sqrt(16)").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 4.0).abs() < 0.001);
        } else {
            panic!("expected float, got {:?}", result);
        }
    }

    #[test]
    fn test_frac_function() {
        let handler = MathBlock;
        let result = handler.evaluate("frac(1, 2)").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 0.5).abs() < 0.001);
        } else {
            panic!("expected float, got {:?}", result);
        }
    }

    #[test]
    fn test_latex_compat_frac() {
        let handler = MathBlock;
        // Should work but emit warning
        let result = handler.evaluate("\\frac{1}{2}").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 0.5).abs() < 0.001);
        } else {
            panic!("expected float, got {:?}", result);
        }
    }

    #[test]
    fn test_latex_compat_sqrt() {
        let handler = MathBlock;
        let result = handler.evaluate("\\sqrt{16}").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 4.0).abs() < 0.001);
        } else {
            panic!("expected float, got {:?}", result);
        }
    }

    #[test]
    fn test_implicit_multiplication() {
        let handler = MathBlock;
        let result = handler.evaluate("2 * 3").unwrap();
        assert_eq!(result, Value::Int(6));
    }

    #[test]
    fn test_power_operator() {
        let handler = MathBlock;
        let result = handler.evaluate("2^3").unwrap();
        if let Value::Float(f) = result {
            assert!((f - 8.0).abs() < 0.001);
        } else {
            panic!("expected float, got {:?}", result);
        }
    }

    #[test]
    fn test_to_latex_simple() {
        let latex = to_latex("2 + 3").unwrap();
        assert_eq!(latex, "2 + 3");
    }

    #[test]
    fn test_to_latex_fraction() {
        let latex = to_latex("frac(1, 2)").unwrap();
        assert_eq!(latex, "\\frac{1}{2}");
    }

    #[test]
    fn test_to_latex_sqrt() {
        let latex = to_latex("sqrt(16)").unwrap();
        assert_eq!(latex, "\\sqrt{16}");
    }

    #[test]
    fn test_to_latex_complex() {
        let latex = to_latex("(2 + 3) * 4").unwrap();
        assert_eq!(latex, "\\left(2 + 3\\right) \\cdot 4");
    }

    #[test]
    fn test_to_latex_from_latex_input() {
        // Input LaTeX, output LaTeX
        let latex = to_latex("\\frac{1}{2}").unwrap();
        assert_eq!(latex, "\\frac{1}{2}");
    }

    // =========================================================================
    // Backend directive parsing tests
    // =========================================================================

    #[test]
    fn test_parse_backend_directive_none() {
        let (payload, backend) = parse_backend_directive("2 + 3");
        assert_eq!(payload, "2 + 3");
        assert_eq!(backend, backend::MathBackend::Auto);
    }

    #[test]
    fn test_parse_backend_directive_cpu() {
        let (payload, backend) = parse_backend_directive("use backend cpu; 2 + 3");
        assert_eq!(payload, "2 + 3");
        assert_eq!(backend, backend::MathBackend::CPU);
    }

    #[test]
    fn test_parse_backend_directive_torch() {
        let (payload, backend) = parse_backend_directive("use backend torch; 1 + 1");
        assert_eq!(payload, "1 + 1");
        assert_eq!(backend, backend::MathBackend::Torch);
    }

    #[test]
    fn test_parse_backend_directive_cuda() {
        let (payload, backend) = parse_backend_directive("use backend cuda; 5 * 5");
        assert_eq!(payload, "5 * 5");
        assert_eq!(backend, backend::MathBackend::CUDA);
    }

    #[test]
    fn test_parse_backend_directive_auto() {
        let (payload, backend) = parse_backend_directive("use backend auto; pi");
        assert_eq!(payload, "pi");
        assert_eq!(backend, backend::MathBackend::Auto);
    }

    #[test]
    fn test_parse_backend_directive_whitespace() {
        let (payload, backend) = parse_backend_directive("use backend cpu  2 + 3");
        assert_eq!(payload, "2 + 3");
        assert_eq!(backend, backend::MathBackend::CPU);
    }

    #[test]
    fn test_parse_backend_directive_unknown() {
        let (_payload, backend) = parse_backend_directive("use backend vulkan; 1");
        assert_eq!(backend, backend::MathBackend::Auto);
    }

    #[test]
    fn test_parse_backend_directive_aliases() {
        // "gpu" → CUDA
        let (_, b) = parse_backend_directive("use backend gpu; 1");
        assert_eq!(b, backend::MathBackend::CUDA);
        // "native" → CPU
        let (_, b) = parse_backend_directive("use backend native; 1");
        assert_eq!(b, backend::MathBackend::CPU);
        // "pytorch" → Torch
        let (_, b) = parse_backend_directive("use backend pytorch; 1");
        assert_eq!(b, backend::MathBackend::Torch);
    }

    // =========================================================================
    // Backend integration tests (full pipeline)
    // =========================================================================

    #[test]
    fn test_evaluate_with_backend_cpu() {
        let handler = MathBlock;
        let result = handler
            .evaluate_with_backend("2 + 3", backend::MathBackend::CPU)
            .unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_evaluate_with_backend_auto() {
        let handler = MathBlock;
        let result = handler
            .evaluate_with_backend("frac(1, 2)", backend::MathBackend::Auto)
            .unwrap();
        if let Value::Float(f) = result {
            assert!((f - 0.5).abs() < 0.001);
        } else {
            panic!("expected float");
        }
    }

    #[test]
    fn test_evaluate_with_backend_torch_fallback() {
        // Torch is unavailable, should fall back to CPU
        let handler = MathBlock;
        let result = handler
            .evaluate_with_backend("3 * 4", backend::MathBackend::Torch)
            .unwrap();
        assert_eq!(result, Value::Int(12));
    }

    #[test]
    fn test_evaluate_with_backend_cuda_fallback() {
        // CUDA is unavailable, should fall back to CPU
        let handler = MathBlock;
        let result = handler
            .evaluate_with_backend("10 - 3", backend::MathBackend::CUDA)
            .unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn test_evaluate_with_backend_directive_in_payload() {
        // Test that `use backend cpu; expr` works through the main evaluate()
        let handler = MathBlock;
        let result = handler.evaluate("use backend cpu; 7 + 8").unwrap();
        assert_eq!(result, Value::Int(15));
    }

    #[test]
    fn test_evaluate_with_backend_matmul() {
        // Matrix operation with auto backend (should pick CPU since Torch/CUDA unavailable)
        let handler = MathBlock;
        let result = handler
            .evaluate_with_backend(
                "matmul([[1, 0], [0, 1]], [[5, 6], [7, 8]])",
                backend::MathBackend::Auto,
            )
            .unwrap();
        if let Value::Array(outer) = result {
            assert_eq!(outer.len(), 2);
        } else {
            panic!("expected array from matmul");
        }
    }

    // =========================================================================
    // Multi-format rendering tests (integration)
    // =========================================================================

    #[test]
    fn test_to_mathml_simple() {
        let mathml = to_mathml("2 + 3").unwrap();
        assert!(mathml.starts_with("<math>"));
        assert!(mathml.ends_with("</math>"));
        assert!(mathml.contains("<mo>+</mo>"));
    }

    #[test]
    fn test_to_text_simple() {
        let text = to_text("2 + 3").unwrap();
        assert_eq!(text, "2 + 3");
    }

    #[test]
    fn test_to_lean_simple() {
        let lean = to_lean("2 + 3").unwrap();
        assert_eq!(lean, "2 + 3");
    }

    #[test]
    fn test_multi_render_frac() {
        let latex = to_latex("frac(1, 2)").unwrap();
        let mathml = to_mathml("frac(1, 2)").unwrap();
        let text = to_text("frac(1, 2)").unwrap();
        let lean = to_lean("frac(1, 2)").unwrap();

        assert_eq!(latex, "\\frac{1}{2}");
        assert!(mathml.contains("<mfrac>"));
        assert_eq!(text, "\u{00bd}"); // ½
        assert_eq!(lean, "1 / 2");
    }

    #[test]
    fn test_multi_render_sqrt_pi() {
        let latex = to_latex("sqrt(pi)").unwrap();
        let mathml = to_mathml("sqrt(pi)").unwrap();
        let text = to_text("sqrt(pi)").unwrap();
        let lean = to_lean("sqrt(pi)").unwrap();

        assert_eq!(latex, "\\sqrt{\\pi}");
        assert!(mathml.contains("<msqrt>"));
        assert!(text.contains("\u{221a}")); // √
        assert!(lean.contains("Real.sqrt"));
        assert!(lean.contains("Real.pi"));
    }
}
