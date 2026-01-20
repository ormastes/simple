//! Statement AST nodes (let, const, static, if, match, for, while, etc.)

use super::super::enums::*;
use super::core::*;
use crate::token::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct LetStmt {
    pub span: Span,
    pub pattern: Pattern,
    pub ty: Option<Type>,
    pub value: Option<Expr>,
    pub mutability: Mutability,
    /// Storage class (Auto for normal variables, Shared for GPU shared memory)
    pub storage_class: StorageClass,
    /// Ghost variable - only exists for verification, erased at runtime
    /// Used in @verify mode for Lean proof generation
    pub is_ghost: bool,
    /// Suspension let binding (val x ~= expr) for async-by-default
    /// When true, the expression is awaited before assignment
    pub is_suspend: bool,
}

/// Compile-time constant declaration
/// const PI = 3.15159
/// const MAX_SIZE: i64 = 100
#[derive(Debug, Clone, PartialEq)]
pub struct ConstStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr, // Required - must be evaluable at compile time
    pub visibility: Visibility,
}

/// Static variable declaration (global, initialized once)
/// static counter = 0
/// static mut config = {}
#[derive(Debug, Clone, PartialEq)]
pub struct StaticStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr, // Required
    pub mutability: Mutability,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignmentStmt {
    pub span: Span,
    pub target: Expr,
    pub op: AssignOp,
    pub value: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Assign,           // =
    AddAssign,        // +=
    SubAssign,        // -=
    MulAssign,        // *=
    DivAssign,        // /=
    SuspendAssign,    // ~= (suspension assignment for async-by-default)
    SuspendAddAssign, // ~+= (suspension compound add)
    SuspendSubAssign, // ~-= (suspension compound subtract)
    SuspendMulAssign, // ~*= (suspension compound multiply)
    SuspendDivAssign, // ~/= (suspension compound divide)
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub span: Span,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub span: Span,
    /// For if-let: the pattern to match against, None for regular if
    pub let_pattern: Option<Pattern>,
    pub condition: Expr,
    pub then_block: Block,
    pub elif_branches: Vec<(Expr, Block)>,
    pub else_block: Option<Block>,
    /// Suspension if statement (if~) for explicit suspension points in async-by-default
    pub is_suspend: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchStmt {
    pub span: Span,
    pub subject: Expr,
    pub arms: Vec<MatchArm>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForStmt {
    pub span: Span,
    pub pattern: Pattern,
    pub iterable: Expr,
    pub body: Block,
    /// Suspension for loop (for~) for explicit suspension points in async-by-default
    pub is_suspend: bool,
    /// Enumerate shorthand: `for i, item in items:` auto-wraps items with indices
    pub auto_enumerate: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub span: Span,
    /// For while-let: the pattern to match against, None for regular while
    pub let_pattern: Option<Pattern>,
    pub condition: Expr,
    pub body: Block,
    /// Suspension while loop (while~) for explicit suspension points in async-by-default
    pub is_suspend: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoopStmt {
    pub span: Span,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BreakStmt {
    pub span: Span,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ContinueStmt {
    pub span: Span,
}

/// Assert statement for inline contract checks
/// assert condition
/// assert condition, "message"
/// check condition  (alias for assert)
#[derive(Debug, Clone, PartialEq)]
pub struct AssertStmt {
    pub span: Span,
    /// The boolean condition to check
    pub condition: Expr,
    /// Optional error message for assertion failure
    pub message: Option<String>,
}

/// Context block for DSL support
/// context expr:
///     statements
#[derive(Debug, Clone, PartialEq)]
pub struct ContextStmt {
    pub span: Span,
    pub context: Expr, // The object that becomes the implicit receiver
    pub body: Block,
}

/// With statement for RAII/context manager pattern
/// with resource as name:
///     statements
#[derive(Debug, Clone, PartialEq)]
pub struct WithStmt {
    pub span: Span,
    pub resource: Expr,       // The resource expression
    pub name: Option<String>, // Optional binding name (as name)
    pub body: Block,
}

/// Lean 4 block for embedding formal verification code
///
/// Supports three forms:
/// 1. Inline: `lean { -- Lean 4 code }`
/// 2. Import: `lean import "proofs/module.lean"`
/// 3. Combined: `lean import "base.lean" { -- extensions }`
///
/// Lean files are generated beside Simple source files.
#[derive(Debug, Clone, PartialEq)]
pub struct LeanBlock {
    pub span: Span,
    /// Optional import path (relative to source file or absolute from project root)
    pub import_path: Option<String>,
    /// Inline Lean 4 code (may be empty if import-only)
    pub code: String,
}
