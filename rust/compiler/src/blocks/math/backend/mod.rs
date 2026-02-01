//! Math computation backend selection and dispatch.
//!
//! Supports multiple computation backends:
//! - CPU: Native interpreter (always available)
//! - Torch: PyTorch tensor backend via FFI
//! - CUDA: Direct CUDA computation via PyTorch
//!
//! Default behavior is auto-selection at runtime based on expression
//! complexity and backend availability.

pub mod auto_select;
pub mod torch_eval;
pub mod cuda_eval;

// Re-export key items for ergonomic access
pub use auto_select::{analyze_complexity, select_backend, BackendSelection};
pub use torch_eval::is_available as torch_available;
pub use torch_eval::is_cuda_available as cuda_available;

/// Computation backend for math expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathBackend {
    /// Runtime auto-select (default) - picks fastest available backend
    Auto,
    /// Native CPU interpreter - always available
    CPU,
    /// PyTorch tensor backend
    Torch,
    /// Direct CUDA computation (via PyTorch CUDA)
    CUDA,
}

impl MathBackend {
    /// Check if this backend is available at runtime.
    pub fn is_available(&self) -> bool {
        match self {
            MathBackend::Auto => true,
            MathBackend::CPU => true,
            MathBackend::Torch => torch_eval::is_available(),
            MathBackend::CUDA => cuda_eval::is_available(),
        }
    }

    /// Get the display name of this backend.
    pub fn name(&self) -> &'static str {
        match self {
            MathBackend::Auto => "Auto",
            MathBackend::CPU => "CPU",
            MathBackend::Torch => "Torch",
            MathBackend::CUDA => "CUDA",
        }
    }
}

impl MathBackend {
    /// Parse a backend from a string name.
    ///
    /// Accepts: "auto", "cpu", "torch", "pytorch", "cuda", "gpu".
    /// Returns `None` for unrecognized names.
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "auto" => Some(MathBackend::Auto),
            "cpu" | "native" => Some(MathBackend::CPU),
            "torch" | "pytorch" => Some(MathBackend::Torch),
            "cuda" | "gpu" => Some(MathBackend::CUDA),
            _ => None,
        }
    }

    /// Evaluate a math expression using this backend.
    ///
    /// Convenience method that dispatches to the appropriate evaluator.
    pub fn evaluate(&self, expr: &crate::blocks::math::ast::MathExpr) -> Result<crate::value::Value, crate::error::CompileError> {
        match self {
            MathBackend::Auto => {
                let complexity = auto_select::analyze_complexity(expr);
                let selection = auto_select::select_backend(&complexity, MathBackend::Auto);
                selection.backend.evaluate(expr)
            }
            MathBackend::CPU => crate::blocks::math::eval::evaluate(expr),
            MathBackend::Torch => torch_eval::evaluate(expr),
            MathBackend::CUDA => cuda_eval::evaluate(expr),
        }
    }
}

impl std::fmt::Display for MathBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Rendering output format for math expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RenderFormat {
    /// LaTeX format
    LaTeX,
    /// MathML XML format
    MathML,
    /// Unicode text
    Text,
    /// Lean4 theorem prover syntax
    Lean,
}

/// Capabilities of a computation backend.
#[derive(Debug, Clone)]
pub struct BackendCapability {
    /// Supports tensor operations
    pub supports_tensor: bool,
    /// Supports automatic differentiation
    pub supports_autograd: bool,
    /// Supports symbolic computation
    pub supports_symbolic: bool,
    /// Maximum precision dtype supported
    pub max_precision: &'static str,
    /// Estimated relative speed (CPU = 1.0)
    pub estimated_speed: f64,
}

impl BackendCapability {
    /// Get capabilities for a given backend.
    pub fn for_backend(backend: MathBackend) -> Self {
        match backend {
            MathBackend::Auto | MathBackend::CPU => BackendCapability {
                supports_tensor: true,
                supports_autograd: false,
                supports_symbolic: true,
                max_precision: "f64",
                estimated_speed: 1.0,
            },
            MathBackend::Torch => BackendCapability {
                supports_tensor: true,
                supports_autograd: true,
                supports_symbolic: false,
                max_precision: "f64",
                estimated_speed: 10.0,
            },
            MathBackend::CUDA => BackendCapability {
                supports_tensor: true,
                supports_autograd: true,
                supports_symbolic: false,
                max_precision: "f64",
                estimated_speed: 50.0,
            },
        }
    }
}

/// Expression complexity hints for backend selection.
#[derive(Debug, Clone)]
pub struct ExprComplexity {
    /// Whether the expression involves tensor operations
    pub has_tensors: bool,
    /// Whether the expression involves matrix operations
    pub has_matrix_ops: bool,
    /// Estimated number of elements involved
    pub estimated_elements: usize,
    /// Whether autograd is needed
    pub needs_autograd: bool,
    /// Whether symbolic computation is needed
    pub needs_symbolic: bool,
}

impl Default for ExprComplexity {
    fn default() -> Self {
        ExprComplexity {
            has_tensors: false,
            has_matrix_ops: false,
            estimated_elements: 1,
            needs_autograd: false,
            needs_symbolic: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocks::math::ast::MathExpr;
    use crate::value::Value;

    #[test]
    fn test_cpu_always_available() {
        assert!(MathBackend::CPU.is_available());
        assert!(MathBackend::Auto.is_available());
    }

    #[test]
    fn test_backend_names() {
        assert_eq!(MathBackend::Auto.name(), "Auto");
        assert_eq!(MathBackend::CPU.name(), "CPU");
        assert_eq!(MathBackend::Torch.name(), "Torch");
        assert_eq!(MathBackend::CUDA.name(), "CUDA");
    }

    #[test]
    fn test_backend_capability() {
        let cpu = BackendCapability::for_backend(MathBackend::CPU);
        assert!(cpu.supports_tensor);
        assert!(!cpu.supports_autograd);
        assert!(cpu.supports_symbolic);

        let torch = BackendCapability::for_backend(MathBackend::Torch);
        assert!(torch.supports_autograd);
        assert!(!torch.supports_symbolic);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", MathBackend::CUDA), "CUDA");
    }

    #[test]
    fn test_from_str() {
        assert_eq!(MathBackend::from_str("auto"), Some(MathBackend::Auto));
        assert_eq!(MathBackend::from_str("cpu"), Some(MathBackend::CPU));
        assert_eq!(MathBackend::from_str("native"), Some(MathBackend::CPU));
        assert_eq!(MathBackend::from_str("torch"), Some(MathBackend::Torch));
        assert_eq!(MathBackend::from_str("pytorch"), Some(MathBackend::Torch));
        assert_eq!(MathBackend::from_str("cuda"), Some(MathBackend::CUDA));
        assert_eq!(MathBackend::from_str("gpu"), Some(MathBackend::CUDA));
        assert_eq!(MathBackend::from_str("TORCH"), Some(MathBackend::Torch));
        assert_eq!(MathBackend::from_str("unknown"), None);
    }

    #[test]
    fn test_backend_evaluate_cpu() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        let result = MathBackend::CPU.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_backend_evaluate_auto() {
        let expr = MathExpr::Mul(Box::new(MathExpr::Int(4)), Box::new(MathExpr::Int(5)));
        let result = MathBackend::Auto.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(20));
    }

    #[test]
    fn test_backend_evaluate_torch_fallback() {
        let expr = MathExpr::Sub(Box::new(MathExpr::Int(10)), Box::new(MathExpr::Int(3)));
        let result = MathBackend::Torch.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(7));
    }

    #[test]
    fn test_backend_evaluate_cuda_fallback() {
        let expr = MathExpr::Int(42);
        let result = MathBackend::CUDA.evaluate(&expr).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    #[test]
    fn test_re_exports() {
        // Verify re-exports work
        assert_eq!(torch_available(), torch_eval::is_available());
        assert_eq!(cuda_available(), torch_eval::is_cuda_available());
    }
}
