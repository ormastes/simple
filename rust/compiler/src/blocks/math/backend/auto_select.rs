//! Runtime auto-selection of computation backend.
//!
//! Scores available backends based on expression complexity and
//! backend capabilities, selecting the fastest suitable option.

use super::{BackendCapability, ExprComplexity, MathBackend};

/// Result of backend selection with reasoning.
#[derive(Debug, Clone)]
pub struct BackendSelection {
    /// The selected backend
    pub backend: MathBackend,
    /// Score that led to selection
    pub score: f64,
    /// Human-readable reason for selection
    pub reason: String,
}

/// Select the best available backend for a given expression.
///
/// If `preferred` is not `Auto` and is available, it will be used.
/// Otherwise, backends are scored and the highest-scoring one is selected.
///
/// All decisions are logged via `tracing::debug!`.
pub fn select_backend(
    complexity: &ExprComplexity,
    preferred: MathBackend,
) -> BackendSelection {
    // If preferred is specified and available, use it
    if preferred != MathBackend::Auto {
        if preferred.is_available() {
            tracing::debug!(
                "[math::backend] Using preferred backend: {}",
                preferred
            );
            return BackendSelection {
                backend: preferred,
                score: f64::MAX,
                reason: format!("Preferred backend: {}", preferred),
            };
        } else {
            tracing::debug!(
                "[math::backend] Preferred {} unavailable, falling back to auto",
                preferred
            );
        }
    }

    // Auto-selection: score each available backend
    let candidates = [MathBackend::CUDA, MathBackend::Torch, MathBackend::CPU];
    let mut best: Option<BackendSelection> = None;

    for &backend in &candidates {
        if !backend.is_available() {
            tracing::debug!("[math::backend] Backend.{}: unavailable", backend);
            continue;
        }

        let cap = BackendCapability::for_backend(backend);

        // Check feature requirements
        if complexity.needs_autograd && !cap.supports_autograd {
            tracing::debug!(
                "[math::backend] Backend.{}: lacks autograd support",
                backend
            );
            continue;
        }
        if complexity.needs_symbolic && !cap.supports_symbolic {
            tracing::debug!(
                "[math::backend] Backend.{}: lacks symbolic support",
                backend
            );
            continue;
        }

        let score = compute_score(backend, complexity);
        tracing::debug!(
            "[math::backend] Backend.{}: available, score={:.1}",
            backend,
            score
        );

        if best.as_ref().map_or(true, |b| score > b.score) {
            best = Some(BackendSelection {
                backend,
                score,
                reason: score_reason(backend, complexity),
            });
        }
    }

    let selection = best.unwrap_or(BackendSelection {
        backend: MathBackend::CPU,
        score: 1.0,
        reason: "Fallback to CPU".to_string(),
    });

    tracing::info!(
        "[math::backend] Auto-selected: {} (score: {:.1}, reason: {})",
        selection.backend,
        selection.score,
        selection.reason
    );

    selection
}

/// Compute a speed score for a backend given expression complexity.
fn compute_score(backend: MathBackend, complexity: &ExprComplexity) -> f64 {
    let n = complexity.estimated_elements;

    match backend {
        MathBackend::CPU | MathBackend::Auto => 1.0,
        MathBackend::Torch => {
            if !complexity.has_tensors && n < 10 {
                0.8 // Overhead from tensor creation
            } else if complexity.has_matrix_ops && n > 1000 {
                10.0
            } else if complexity.has_matrix_ops && n > 100 {
                3.0
            } else if complexity.has_matrix_ops {
                1.2
            } else {
                1.5
            }
        }
        MathBackend::CUDA => {
            if !complexity.has_tensors && n < 100 {
                0.3 // Too much overhead for small ops
            } else if complexity.has_matrix_ops && n > 1000 {
                50.0
            } else if complexity.has_matrix_ops && n > 100 {
                5.0
            } else if n > 1000 {
                15.0
            } else {
                2.0
            }
        }
    }
}

/// Generate a human-readable reason for the score.
fn score_reason(backend: MathBackend, complexity: &ExprComplexity) -> String {
    match backend {
        MathBackend::CPU | MathBackend::Auto => "baseline CPU".to_string(),
        MathBackend::Torch => {
            if complexity.has_matrix_ops && complexity.estimated_elements > 1000 {
                "large matrix ops".to_string()
            } else if complexity.has_tensors {
                "tensor operations".to_string()
            } else {
                "general computation".to_string()
            }
        }
        MathBackend::CUDA => {
            if complexity.has_matrix_ops && complexity.estimated_elements > 1000 {
                "large matrix ops on GPU".to_string()
            } else if complexity.estimated_elements > 1000 {
                "large reduction op".to_string()
            } else {
                "GPU acceleration".to_string()
            }
        }
    }
}

/// Analyze a MathExpr to determine its complexity hints.
pub fn analyze_complexity(expr: &crate::blocks::math::ast::MathExpr) -> ExprComplexity {
    use crate::blocks::math::ast::MathExpr;

    let mut complexity = ExprComplexity::default();
    analyze_expr(expr, &mut complexity);
    complexity
}

fn analyze_expr(
    expr: &crate::blocks::math::ast::MathExpr,
    complexity: &mut ExprComplexity,
) {
    use crate::blocks::math::ast::MathExpr;

    match expr {
        MathExpr::Array(elements) => {
            complexity.has_tensors = true;
            complexity.estimated_elements = complexity.estimated_elements.max(elements.len());
            if matches!(elements.first(), Some(MathExpr::Array(_))) {
                complexity.has_matrix_ops = true;
                if let Some(MathExpr::Array(inner)) = elements.first() {
                    complexity.estimated_elements =
                        complexity.estimated_elements.max(elements.len() * inner.len());
                }
            }
            for e in elements {
                analyze_expr(e, complexity);
            }
        }
        MathExpr::App(name, args) => {
            match name.as_str() {
                "matmul" | "dot" | "transpose" | "reshape" => {
                    complexity.has_matrix_ops = true;
                    complexity.has_tensors = true;
                }
                "zeros" | "ones" | "rand" | "randn" | "eye" | "tensor"
                | "full" | "arange" | "linspace" => {
                    complexity.has_tensors = true;
                }
                _ => {}
            }
            for a in args {
                analyze_expr(a, complexity);
            }
        }
        MathExpr::Sum { range, body, .. }
        | MathExpr::Prod { range, body, .. }
        | MathExpr::Integral { range, body, .. } => {
            // Estimate iteration count from range
            if let (MathExpr::Int(start), MathExpr::Int(end)) = (&range.start, &range.end) {
                let count = (*end - *start).unsigned_abs() as usize;
                complexity.estimated_elements = complexity.estimated_elements.max(count);
            }
            analyze_expr(body, complexity);
        }
        MathExpr::Add(l, r) | MathExpr::Sub(l, r) | MathExpr::Mul(l, r)
        | MathExpr::Div(l, r) | MathExpr::Pow(l, r) | MathExpr::Mod(l, r)
        | MathExpr::Eq(l, r) | MathExpr::Neq(l, r) | MathExpr::Lt(l, r)
        | MathExpr::Le(l, r) | MathExpr::Gt(l, r) | MathExpr::Ge(l, r)
        | MathExpr::Approx(l, r) => {
            analyze_expr(l, complexity);
            analyze_expr(r, complexity);
        }
        MathExpr::Neg(inner) | MathExpr::Abs(inner) | MathExpr::Group(inner) => {
            analyze_expr(inner, complexity);
        }
        MathExpr::Subscript(base, idx) => {
            analyze_expr(base, complexity);
            analyze_expr(idx, complexity);
        }
        MathExpr::Int(_) | MathExpr::Float(_) | MathExpr::Var(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocks::math::ast::{MathExpr, Range};

    #[test]
    fn test_auto_select_cpu_for_simple() {
        let complexity = ExprComplexity::default();
        let result = select_backend(&complexity, MathBackend::Auto);
        assert_eq!(result.backend, MathBackend::CPU);
    }

    #[test]
    fn test_preferred_backend() {
        let complexity = ExprComplexity::default();
        let result = select_backend(&complexity, MathBackend::CPU);
        assert_eq!(result.backend, MathBackend::CPU);
    }

    #[test]
    fn test_analyze_simple_expr() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(1)), Box::new(MathExpr::Int(2)));
        let complexity = analyze_complexity(&expr);
        assert!(!complexity.has_tensors);
        assert!(!complexity.has_matrix_ops);
    }

    #[test]
    fn test_analyze_matrix_expr() {
        let expr = MathExpr::App(
            "matmul".to_string(),
            vec![
                MathExpr::Array(vec![
                    MathExpr::Array(vec![MathExpr::Int(1), MathExpr::Int(2)]),
                    MathExpr::Array(vec![MathExpr::Int(3), MathExpr::Int(4)]),
                ]),
                MathExpr::Var("B".to_string()),
            ],
        );
        let complexity = analyze_complexity(&expr);
        assert!(complexity.has_tensors);
        assert!(complexity.has_matrix_ops);
    }

    #[test]
    fn test_analyze_sum_complexity() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Int(1000))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        let complexity = analyze_complexity(&expr);
        assert!(complexity.estimated_elements >= 999);
    }

    #[test]
    fn test_symbolic_needs_cpu() {
        let complexity = ExprComplexity {
            needs_symbolic: true,
            ..Default::default()
        };
        let result = select_backend(&complexity, MathBackend::Auto);
        // CPU supports symbolic, Torch/CUDA don't
        assert_eq!(result.backend, MathBackend::CPU);
    }
}
