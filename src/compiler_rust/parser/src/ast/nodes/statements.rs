//! Statement AST nodes (let, const, static, if, match, for, while, etc.)

use super::super::enums::*;
use super::contracts::ContractClause;
use super::core::*;
use super::definitions::FunctionDef;
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
    ModAssign,        // %=
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
    pub elif_branches: Vec<(Option<Pattern>, Expr, Block)>,
    pub else_block: Option<Block>,
    /// Suspension if statement (if~) for explicit suspension points in async-by-default
    pub is_suspend: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchStmt {
    pub span: Span,
    pub subject: Expr,
    pub arms: Vec<MatchArm>,
    /// Suspension match statement (match~) for explicit suspension points in async-by-default
    pub is_suspend: bool,
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
    /// Loop invariants for verification
    /// ```simple
    /// for i in 0..n:
    ///     invariant: sum == partial_sum(i)
    ///     sum = sum + arr[i]
    /// ```
    pub invariants: Vec<ContractClause>,
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
    /// Loop invariants for verification
    /// ```simple
    /// while x > 0:
    ///     invariant: x * y == original
    ///     x = x - 1
    ///     y = y + 1
    /// ```
    pub invariants: Vec<ContractClause>,
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

/// Pass statement (no-op, like Python's pass)
/// Used to have an empty block body
#[derive(Debug, Clone, PartialEq)]
pub struct PassStmt {
    pub span: Span,
}

/// Skip statement (no-op, similar to pass, used for test skipping context)
/// Can mark sections of code to be skipped during execution or test discovery
#[derive(Debug, Clone, PartialEq)]
pub struct SkipStmt {
    pub span: Span,
    pub body: SkipBody,
}

/// Body of a skip statement
#[derive(Debug, Clone, PartialEq)]
pub enum SkipBody {
    /// Standalone statement: `skip`
    Standalone,
    /// Block of statements: `skip: body`
    Block(Block),
}

/// Defer statement - execute at scope exit (LIFO order)
///
/// Deferred statements run when the enclosing scope exits, whether by:
/// - Normal flow (end of function/block)
/// - Early return
/// - Break/continue in loops
/// - Exception propagation
///
/// # Syntax
/// ```simple
/// defer file.close()              # Single expression
/// defer:                          # Block form
///     cleanup_resource()
///     log("done")
/// ```
///
/// # Semantics
/// - LIFO: later defers run first
/// - Variables captured at defer time (closure semantics)
/// - Runs even on error propagation
#[derive(Debug, Clone, PartialEq)]
pub struct DeferStmt {
    pub span: Span,
    /// The deferred action - either a single expression or a block
    pub body: DeferBody,
}

/// Body of a defer statement
#[derive(Debug, Clone, PartialEq)]
pub enum DeferBody {
    /// Single expression: `defer file.close()`
    Expr(Expr),
    /// Block of statements: `defer: statements`
    Block(Block),
}

/// Guard clause statement: `? condition -> result` or `? else -> result`
/// Desugars to early return if condition is true.
///
/// # Example
/// ```simple
/// fn divide(x: i64, y: i64) -> Option<i64>:
///     ? y == 0 -> None       # Early return if y is 0
///     Some(x / y)
///
/// fn process(data: Option<Data>):
///     ? data.is_none() -> return   # Early return if no data
///     val d = data.unwrap()
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct GuardStmt {
    pub span: Span,
    /// The condition to check (None if this is `? else -> result`)
    pub condition: Option<Expr>,
    /// The result expression if condition is true
    pub result: Expr,
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

/// Assume statement for verification assumptions
/// assume condition
/// assume condition, "message"
/// In verification: creates a hypothesis without proof
/// At runtime: behaves like assert (debug mode) or is erased (release mode)
#[derive(Debug, Clone, PartialEq)]
pub struct AssumeStmt {
    pub span: Span,
    /// The boolean condition assumed to be true
    pub condition: Expr,
    /// Optional documentation message explaining the assumption
    pub message: Option<String>,
}

/// Admit statement for skipping proofs (tracked)
/// admit condition, "reason"
/// In verification: marks as axiom, requires tracking
/// At runtime: behaves like assert
/// Admits are tracked and reported during compilation
#[derive(Debug, Clone, PartialEq)]
pub struct AdmitStmt {
    pub span: Span,
    /// The boolean condition being admitted without proof
    pub condition: Expr,
    /// Required reason explaining why the proof is being skipped
    pub message: Option<String>,
}

/// Proof hint statement for guiding Lean proof tactics (VER-020)
/// lean hint: "simp"
/// lean hint: "simp [factorial, Nat.mul_pos, *]"
/// In verification: provides tactic hint for Lean prover
/// At runtime: no effect (erased)
#[derive(Debug, Clone, PartialEq)]
pub struct ProofHintStmt {
    pub span: Span,
    /// The tactic or hint string to pass to Lean
    pub hint: String,
}

/// Calculational proof block for step-by-step equational reasoning (VER-021)
/// ```simple
/// calc:
///     sum(0..=n)
///     == sum(0..n) + n        by: "definition"
///     == (n-1)*n/2 + n        by: "induction hypothesis"
///     == n * (n + 1) / 2      by: "factor"
/// ```
/// In verification: generates Lean calc proof
/// At runtime: no effect (erased)
#[derive(Debug, Clone, PartialEq)]
pub struct CalcStmt {
    pub span: Span,
    /// The calculational steps: each step is (expression, justification)
    /// The first expression is the starting term
    pub steps: Vec<CalcStep>,
}

/// A single step in a calculational proof
#[derive(Debug, Clone, PartialEq)]
pub struct CalcStep {
    pub span: Span,
    /// The expression in this step
    pub expr: Expr,
    /// Optional justification string (by: "reason")
    pub justification: Option<String>,
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

/// Inline assembly statement: `asm: "instruction"` or `asm: block`
/// Also supports target-conditional: `asm match: case [target]: instructions`
/// Also supports volatile forms: `asm volatile: block` and `asm volatile(...)`
#[derive(Debug, Clone, PartialEq)]
pub struct InlineAsmStmt {
    pub span: Span,
    /// Whether the `volatile` keyword was present
    pub volatile: bool,
    /// Assembly instructions (one per line in block form)
    pub instructions: Vec<String>,
    /// Target-conditional arms: `asm match: case [target]: instructions`
    pub target_match: Vec<AsmTargetArm>,
    /// Clobber registers declared by this asm block
    pub clobbers: Vec<String>,
    /// Operand constraints (in/out/inout/lateout/clobber_abi/options)
    pub constraints: Vec<AsmConstraint>,
}

/// An operand constraint in an inline assembly statement.
/// Examples:
///   `in(reg) expr` / `out(reg) var` / `name = in(reg) expr`
///   `clobber_abi("C")` / `options(nostack)`
#[derive(Debug, Clone, PartialEq)]
pub struct AsmConstraint {
    pub span: Span,
    /// Optional binding name (e.g., `op` in `op = in(reg) expr`)
    pub name: Option<String>,
    /// The constraint direction/kind
    pub kind: AsmConstraintKind,
    /// Register class (e.g., "reg") - None for clobber_abi/options
    pub reg_class: Option<String>,
    /// The operand expression - None for clobber_abi/options
    pub operand: Option<Expr>,
}

/// Direction/kind of an asm operand constraint
#[derive(Debug, Clone, PartialEq)]
pub enum AsmConstraintKind {
    /// Input operand: `in(reg) expr`
    In,
    /// Output operand: `out(reg) var`
    Out,
    /// Input+output operand: `inout(reg) var`
    InOut,
    /// Late output operand: `lateout(reg) var`
    LateOut,
    /// Clobber register: `clobber(reg)`
    Clobber,
    /// Clobber ABI: `clobber_abi("C")`
    ClobberAbi(String),
    /// Options: `options(nostack)` etc.
    Options(Vec<String>),
}

/// Target-conditional arm in asm match
#[derive(Debug, Clone, PartialEq)]
pub struct AsmTargetArm {
    pub span: Span,
    /// Target platform pattern (e.g., "x86_64", "aarch64", "_" for default)
    pub target: String,
    /// Instructions for this target
    pub instructions: Vec<String>,
}

/// Newtype definition: `newtype Name = Type`
/// Creates a wrapper struct with a single `value` field.
#[derive(Debug, Clone, PartialEq)]
pub struct NewtypeDef {
    pub span: Span,
    pub name: String,
    /// The wrapped type
    pub inner_type: Type,
    pub visibility: Visibility,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
}

/// Extend block: `extend TypeName: methods`
/// Adds methods to an existing type (like Rust's impl blocks without traits).
#[derive(Debug, Clone, PartialEq)]
pub struct ExtendBlock {
    pub span: Span,
    /// The type being extended
    pub target_type: String,
    /// Generic type parameters
    pub generic_params: Vec<String>,
    /// Methods to add
    pub methods: Vec<FunctionDef>,
}
