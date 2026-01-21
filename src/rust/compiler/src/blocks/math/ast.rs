//! Math expression AST.
//!
//! Provides a semantic AST for mathematical expressions that can be:
//! - Evaluated to numeric values
//! - Exported to MathML/LaTeX/Lean
//! - Type-checked for tensor operations

/// Math expression AST node
#[derive(Debug, Clone, PartialEq)]
pub enum MathExpr {
    // === Literals ===
    /// Integer literal: 42
    Int(i64),
    /// Float literal: 3.14
    Float(f64),
    /// Array literal for tensor creation: [1, 2, 3] or [[1, 2], [3, 4]]
    Array(Vec<MathExpr>),

    // === Identifiers ===
    /// Variable or constant: x, pi, alpha
    Var(String),

    // === Binary operators ===
    /// Addition: a + b
    Add(Box<MathExpr>, Box<MathExpr>),
    /// Subtraction: a - b
    Sub(Box<MathExpr>, Box<MathExpr>),
    /// Multiplication: a * b, a · b, or implicit (2x)
    Mul(Box<MathExpr>, Box<MathExpr>),
    /// Division: a / b
    Div(Box<MathExpr>, Box<MathExpr>),
    /// Power: a ^ b
    Pow(Box<MathExpr>, Box<MathExpr>),
    /// Modulo: a % b
    Mod(Box<MathExpr>, Box<MathExpr>),

    // === Unary operators ===
    /// Negation: -x
    Neg(Box<MathExpr>),
    /// Absolute value: |x| or abs(x)
    Abs(Box<MathExpr>),

    // === Functions ===
    /// Function application: f(args...)
    /// Includes: sqrt, sin, cos, tan, log, exp, frac, etc.
    App(String, Vec<MathExpr>),

    // === Subscript/Superscript ===
    /// Subscript: x[i] or x_i
    Subscript(Box<MathExpr>, Box<MathExpr>),

    // === Grouping ===
    /// Parenthesized expression
    Group(Box<MathExpr>),

    // === Binders (big operators) ===
    /// Summation: sum(var, range) body
    Sum {
        var: String,
        range: Box<Range>,
        body: Box<MathExpr>,
    },
    /// Product: prod(var, range) body
    Prod {
        var: String,
        range: Box<Range>,
        body: Box<MathExpr>,
    },
    /// Integral: int(var, range) body
    Integral {
        var: String,
        range: Box<Range>,
        body: Box<MathExpr>,
    },

    // === Comparison ===
    /// Equality: a = b (in math context)
    Eq(Box<MathExpr>, Box<MathExpr>),
    /// Not equal: a != b or a ≠ b
    Neq(Box<MathExpr>, Box<MathExpr>),
    /// Less than: a < b
    Lt(Box<MathExpr>, Box<MathExpr>),
    /// Less than or equal: a <= b or a ≤ b
    Le(Box<MathExpr>, Box<MathExpr>),
    /// Greater than: a > b
    Gt(Box<MathExpr>, Box<MathExpr>),
    /// Greater than or equal: a >= b or a ≥ b
    Ge(Box<MathExpr>, Box<MathExpr>),
    /// Approximately equal: a ≈ b
    Approx(Box<MathExpr>, Box<MathExpr>),
}

/// Range specification for binders
#[derive(Debug, Clone, PartialEq)]
pub struct Range {
    pub start: MathExpr,
    pub end: MathExpr,
}

impl Range {
    pub fn new(start: MathExpr, end: MathExpr) -> Self {
        Self { start, end }
    }
}

/// Built-in math constants
pub fn get_constant(name: &str) -> Option<f64> {
    match name {
        // Greek letters as constants
        "pi" | "π" => Some(std::f64::consts::PI),
        "tau" | "τ" => Some(std::f64::consts::TAU),
        "e" => Some(std::f64::consts::E),
        "phi" | "φ" => Some(1.618033988749895), // Golden ratio
        "inf" | "∞" => Some(f64::INFINITY),
        _ => None,
    }
}

/// Check if a name is a built-in math function
pub fn is_builtin_function(name: &str) -> bool {
    matches!(
        name,
        // Basic functions
        "sqrt" | "√" | "cbrt" |
        "abs" |
        "floor" | "ceil" | "round" | "trunc" |
        "sign" | "sgn" |
        // Trigonometric
        "sin" | "cos" | "tan" |
        "asin" | "arcsin" | "acos" | "arccos" | "atan" | "arctan" |
        "sinh" | "cosh" | "tanh" |
        "asinh" | "acosh" | "atanh" |
        // Exponential/logarithmic
        "exp" | "log" | "ln" | "log10" | "log2" |
        // Special functions
        "frac" |
        "root" |
        "min" | "max" |
        "gcd" | "lcm" |
        "factorial" | "fact" |
        "binomial" | "binom" |
        // Binders (parsed specially but also callable)
        "sum" | "Σ" |
        "prod" | "Π" |
        "int" | "∫" |
        // Tensor creation (torch-compatible)
        "tensor" | "zeros" | "ones" | "full" | "eye" |
        "arange" | "linspace" | "rand" | "randn" |
        // Tensor operations
        "matmul" | "dot" | "transpose" | "T" |
        "reshape" | "flatten" | "squeeze" | "unsqueeze" |
        "shape" | "ndim" | "numel" | "item" |
        // Tensor reductions
        "mean" | "var" | "std" | "argmin" | "argmax" |
        // Tensor element-wise (also work on scalars)
        "relu" | "sigmoid" | "softmax" |
        // Tensor utilities
        "cat" | "stack" | "split" | "chunk"
    )
}

/// Normalize function name (handle Unicode aliases)
pub fn normalize_function_name(name: &str) -> &str {
    match name {
        "√" => "sqrt",
        "Σ" => "sum",
        "Π" => "prod",
        "∫" => "int",
        "arcsin" => "asin",
        "arccos" => "acos",
        "arctan" => "atan",
        "ln" => "log",
        "sgn" => "sign",
        "fact" => "factorial",
        "binom" => "binomial",
        _ => name,
    }
}

impl MathExpr {
    /// Convert expression to LaTeX format
    pub fn to_latex(&self) -> String {
        match self {
            // Literals
            MathExpr::Int(n) => n.to_string(),
            MathExpr::Float(f) => {
                // Format float nicely
                if f.fract() == 0.0 && f.abs() < 1e10 {
                    format!("{:.0}", f)
                } else {
                    f.to_string()
                }
            }
            MathExpr::Array(elements) => {
                // Arrays as column vectors or matrices
                if elements.is_empty() {
                    return "\\begin{bmatrix}\\end{bmatrix}".to_string();
                }
                // Check if it's a matrix (array of arrays)
                if matches!(elements[0], MathExpr::Array(_)) {
                    let rows: Vec<String> = elements
                        .iter()
                        .map(|row| {
                            if let MathExpr::Array(cols) = row {
                                cols.iter().map(|e| e.to_latex()).collect::<Vec<_>>().join(" & ")
                            } else {
                                row.to_latex()
                            }
                        })
                        .collect();
                    format!("\\begin{{bmatrix}}\n{}\n\\end{{bmatrix}}", rows.join(" \\\\\n"))
                } else {
                    // Column vector
                    let rows: Vec<String> = elements.iter().map(|e| e.to_latex()).collect();
                    format!("\\begin{{bmatrix}}\n{}\n\\end{{bmatrix}}", rows.join(" \\\\\n"))
                }
            }

            // Variables and constants
            MathExpr::Var(name) => {
                // Map to Greek letters
                match name.as_str() {
                    "alpha" => "\\alpha".to_string(),
                    "beta" => "\\beta".to_string(),
                    "gamma" => "\\gamma".to_string(),
                    "delta" => "\\delta".to_string(),
                    "epsilon" => "\\epsilon".to_string(),
                    "theta" => "\\theta".to_string(),
                    "lambda" => "\\lambda".to_string(),
                    "mu" => "\\mu".to_string(),
                    "pi" => "\\pi".to_string(),
                    "sigma" => "\\sigma".to_string(),
                    "tau" => "\\tau".to_string(),
                    "phi" => "\\phi".to_string(),
                    "omega" => "\\omega".to_string(),
                    _ => name.clone(),
                }
            }

            // Binary operators
            MathExpr::Add(left, right) => format!("{} + {}", left.to_latex(), right.to_latex()),
            MathExpr::Sub(left, right) => format!("{} - {}", left.to_latex(), right.to_latex()),
            MathExpr::Mul(left, right) => {
                // Use \cdot for explicit multiplication
                format!("{} \\cdot {}", left.to_latex(), right.to_latex())
            }
            MathExpr::Div(left, right) => {
                format!("\\frac{{{}}}{{{}}}", left.to_latex(), right.to_latex())
            }
            MathExpr::Pow(base, exp) => format!("{{{}}}^{{{}}}", base.to_latex(), exp.to_latex()),
            MathExpr::Mod(left, right) => {
                format!("{} \\bmod {}", left.to_latex(), right.to_latex())
            }

            // Unary operators
            MathExpr::Neg(expr) => format!("-{}", expr.to_latex()),
            MathExpr::Abs(expr) => format!("\\left|{}\\right|", expr.to_latex()),

            // Functions
            MathExpr::App(name, args) => {
                match name.as_str() {
                    "frac" if args.len() == 2 => {
                        format!("\\frac{{{}}}{{{}}}", args[0].to_latex(), args[1].to_latex())
                    }
                    "sqrt" if args.len() == 1 => format!("\\sqrt{{{}}}", args[0].to_latex()),
                    "sin" | "cos" | "tan" | "log" | "ln" | "exp" => {
                        let args_str: Vec<String> = args.iter().map(|a| a.to_latex()).collect();
                        format!("\\{} {}", name, args_str.join(", "))
                    }
                    "matmul" | "dot" | "transpose" | "reshape" | "zeros" | "ones" | "eye" | "arange" | "linspace"
                    | "rand" | "randn" | "mean" | "sum" | "var" | "std" | "min" | "max" | "relu" | "sigmoid"
                    | "softmax" | "tanh" => {
                        // Tensor operations - use text mode
                        let args_str: Vec<String> = args.iter().map(|a| a.to_latex()).collect();
                        format!("\\text{{{}}}({})", name, args_str.join(", "))
                    }
                    _ => {
                        let args_str: Vec<String> = args.iter().map(|a| a.to_latex()).collect();
                        format!("{}({})", name, args_str.join(", "))
                    }
                }
            }

            // Subscript
            MathExpr::Subscript(base, index) => {
                format!("{}_{{{}}}", base.to_latex(), index.to_latex())
            }

            // Grouping
            MathExpr::Group(expr) => format!("\\left({}\\right)", expr.to_latex()),

            // Binders
            MathExpr::Sum { var, range, body } => {
                format!(
                    "\\sum_{{{}={}}}^{{{}}} {}",
                    var,
                    range.start.to_latex(),
                    range.end.to_latex(),
                    body.to_latex()
                )
            }
            MathExpr::Prod { var, range, body } => {
                format!(
                    "\\prod_{{{}={}}}^{{{}}} {}",
                    var,
                    range.start.to_latex(),
                    range.end.to_latex(),
                    body.to_latex()
                )
            }
            MathExpr::Integral { var, range, body } => {
                format!(
                    "\\int_{{{}}}^{{{}}} {} \\, d{}",
                    range.start.to_latex(),
                    range.end.to_latex(),
                    body.to_latex(),
                    var
                )
            }

            // Comparison operators
            MathExpr::Eq(left, right) => format!("{} = {}", left.to_latex(), right.to_latex()),
            MathExpr::Neq(left, right) => format!("{} \\neq {}", left.to_latex(), right.to_latex()),
            MathExpr::Lt(left, right) => format!("{} < {}", left.to_latex(), right.to_latex()),
            MathExpr::Le(left, right) => format!("{} \\leq {}", left.to_latex(), right.to_latex()),
            MathExpr::Gt(left, right) => format!("{} > {}", left.to_latex(), right.to_latex()),
            MathExpr::Ge(left, right) => format!("{} \\geq {}", left.to_latex(), right.to_latex()),
            MathExpr::Approx(left, right) => {
                format!("{} \\approx {}", left.to_latex(), right.to_latex())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_latex_basic_arithmetic() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        assert_eq!(expr.to_latex(), "2 + 3");
    }

    #[test]
    fn test_latex_fraction() {
        let expr = MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)]);
        assert_eq!(expr.to_latex(), "\\frac{1}{2}");
    }

    #[test]
    fn test_latex_sqrt() {
        let expr = MathExpr::App("sqrt".to_string(), vec![MathExpr::Int(16)]);
        assert_eq!(expr.to_latex(), "\\sqrt{16}");
    }

    #[test]
    fn test_latex_power() {
        let expr = MathExpr::Pow(Box::new(MathExpr::Var("x".to_string())), Box::new(MathExpr::Int(2)));
        assert_eq!(expr.to_latex(), "{x}^{2}");
    }

    #[test]
    fn test_latex_greek_letters() {
        let expr = MathExpr::Var("pi".to_string());
        assert_eq!(expr.to_latex(), "\\pi");

        let expr = MathExpr::Var("alpha".to_string());
        assert_eq!(expr.to_latex(), "\\alpha");
    }

    #[test]
    fn test_latex_sum() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Var("n".to_string()))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        assert_eq!(expr.to_latex(), "\\sum_{i=1}^{n} i");
    }

    #[test]
    fn test_latex_integral() {
        let expr = MathExpr::Integral {
            var: "x".to_string(),
            range: Box::new(Range::new(MathExpr::Int(0), MathExpr::Int(1))),
            body: Box::new(MathExpr::Var("x".to_string())),
        };
        assert_eq!(expr.to_latex(), "\\int_{0}^{1} x \\, dx");
    }

    #[test]
    fn test_latex_array_vector() {
        let expr = MathExpr::Array(vec![MathExpr::Int(1), MathExpr::Int(2), MathExpr::Int(3)]);
        assert!(expr.to_latex().contains("\\begin{bmatrix}"));
        assert!(expr.to_latex().contains("\\end{bmatrix}"));
    }

    #[test]
    fn test_latex_array_matrix() {
        let expr = MathExpr::Array(vec![
            MathExpr::Array(vec![MathExpr::Int(1), MathExpr::Int(2)]),
            MathExpr::Array(vec![MathExpr::Int(3), MathExpr::Int(4)]),
        ]);
        let latex = expr.to_latex();
        assert!(latex.contains("\\begin{bmatrix}"));
        assert!(latex.contains("1 & 2"));
        assert!(latex.contains("3 & 4"));
        assert!(latex.contains("\\end{bmatrix}"));
    }

    #[test]
    fn test_latex_complex_expr() {
        // (2 + 3) * 4
        let expr = MathExpr::Mul(
            Box::new(MathExpr::Group(Box::new(MathExpr::Add(
                Box::new(MathExpr::Int(2)),
                Box::new(MathExpr::Int(3)),
            )))),
            Box::new(MathExpr::Int(4)),
        );
        assert_eq!(expr.to_latex(), "\\left(2 + 3\\right) \\cdot 4");
    }
}
