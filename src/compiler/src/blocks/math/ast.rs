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
        "int" | "∫"
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
