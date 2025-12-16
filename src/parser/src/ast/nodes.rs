use crate::token::{NumericSuffix, Span};
use super::enums::*;

/// All AST node types
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    // Definitions
    Function(FunctionDef),
    Struct(StructDef),
    Class(ClassDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplBlock),
    Actor(ActorDef),
    TypeAlias(TypeAliasDef),
    Extern(ExternDef),
    Macro(MacroDef),
    Unit(UnitDef),
    UnitFamily(UnitFamilyDef),

    // Module system (Features #104-111)
    ModDecl(ModDecl),
    UseStmt(UseStmt),
    CommonUseStmt(CommonUseStmt),
    ExportUseStmt(ExportUseStmt),
    AutoImportStmt(AutoImportStmt),

    // Statements
    Let(LetStmt),
    Const(ConstStmt),
    Static(StaticStmt),
    Assignment(AssignmentStmt),
    Return(ReturnStmt),
    If(IfStmt),
    Match(MatchStmt),
    For(ForStmt),
    While(WhileStmt),
    Loop(LoopStmt),
    Break(BreakStmt),
    Continue(ContinueStmt),
    Context(ContextStmt),
    With(WithStmt),
    Expression(Expr),
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

/// Decorator applied to a function: @decorator or @decorator(args)
#[derive(Debug, Clone, PartialEq)]
pub struct Decorator {
    pub span: Span,
    pub name: Expr,              // The decorator expression (e.g., Identifier or Call)
    pub args: Option<Vec<Expr>>, // Arguments if @decorator(args)
}

/// Attribute applied to an item: #[name] or #[name = "value"] or #[name(args)]
/// Attributes provide compile-time metadata for items like functions and classes.
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
    pub span: Span,
    pub name: String,            // The attribute name (e.g., "inline", "deprecated")
    pub value: Option<Expr>,     // Optional value: #[name = value]
    pub args: Option<Vec<Expr>>, // Optional arguments: #[name(arg1, arg2)]
}

/// Documentation comment parsed from block comments /** ... */ or line comments starting with ##
///
/// Doc comments are used directly as API descriptions. Parameters should have
/// descriptive names (self-documenting). Inline comments can be added to params
/// and return types in the code itself.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct DocComment {
    /// The documentation text (used directly as API description)
    pub content: String,
}

impl DocComment {
    /// Create a DocComment from raw content.
    /// The content is used directly as the API description.
    pub fn new(content: String) -> Self {
        DocComment {
            content: content.trim().to_string(),
        }
    }
}

/// A single where bound: `T: Trait1 + Trait2`
///
/// Example:
/// ```simple
/// fn make[T]() -> T where T: Clone + Default:
///     return T.default()
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct WhereBound {
    pub span: Span,
    /// The type parameter being constrained (e.g., "T")
    pub type_param: String,
    /// The trait bounds (e.g., ["Clone", "Default"])
    pub bounds: Vec<String>,
}

/// A where clause containing multiple bounds
pub type WhereClause = Vec<WhereBound>;

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: fn foo<T, U>(...)
    pub generic_params: Vec<String>,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub body: Block,
    pub visibility: Visibility,
    pub effect: Option<Effect>,
    /// Decorators applied to the function: @decorator
    pub decorators: Vec<Decorator>,
    /// Attributes applied to the function: #[inline], #[deprecated]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
    /// Contract specification (requires/ensures)
    pub contract: Option<ContractBlock>,
    /// Whether this is an abstract method (trait method without body)
    pub is_abstract: bool,
}

impl FunctionDef {
    /// Check if this function is marked as pure via #[pure] attribute (CTR-031)
    /// Pure functions can be called from contract expressions.
    pub fn is_pure(&self) -> bool {
        self.attributes.iter().any(|attr| attr.name == "pure")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub default: Option<Expr>,
    pub mutability: Mutability,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub span: Span,
    pub statements: Vec<Node>,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            span: Span::new(0, 0, 0, 0),
            statements: Vec::new(),
        }
    }
}

//==============================================================================
// Contract Blocks (LLM-friendly feature #400)
// Spec: doc/spec/invariant.md
//==============================================================================

/// Contract specification for a function.
///
/// Contracts make function behavior explicit and verifiable, which helps
/// catch LLM-generated code errors at runtime (and optionally at compile time).
///
/// New spec syntax (doc/spec/invariant.md):
/// ```simple
/// fn div(a: i64, b: i64) -> (i64 | DivByZero):
///     in:
///         b != 0
///     invariant:
///         true
///
///     if b == 0:
///         return DivByZero(msg: "division by zero")
///     return a / b
///
///     out(ret):
///         ret * b == a
///     out_err(err):
///         old(b) == 0
/// ```
///
/// Legacy syntax (still supported):
/// ```simple
/// fn divide(a: i64, b: i64) -> i64:
///     requires:
///         b != 0
///     ensures:
///         result * b == a
///     return a / b
/// ```
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ContractBlock {
    /// Preconditions (in: block) - must be true at function entry
    /// Legacy: requires: block
    pub preconditions: Vec<ContractClause>,
    /// Routine invariants (invariant: block inside function)
    /// Must be true at entry and all exits
    pub invariants: Vec<ContractClause>,
    /// Postconditions for success (out(ret): block)
    /// Legacy: ensures: block
    /// The binding name for return value (default: "ret")
    pub postconditions: Vec<ContractClause>,
    pub postcondition_binding: Option<String>,
    /// Postconditions for error exit (out_err(err): block)
    /// The binding name for error value (default: "err")
    pub error_postconditions: Vec<ContractClause>,
    pub error_binding: Option<String>,
}

impl ContractBlock {
    /// Check if the contract block is empty (no clauses)
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.invariants.is_empty()
            && self.postconditions.is_empty()
            && self.error_postconditions.is_empty()
    }

    /// Legacy compatibility: get requires clauses
    pub fn requires(&self) -> &[ContractClause] {
        &self.preconditions
    }

    /// Legacy compatibility: get ensures clauses
    pub fn ensures(&self) -> &[ContractClause] {
        &self.postconditions
    }
}

/// A single contract clause (one condition in contract blocks).
#[derive(Debug, Clone, PartialEq)]
pub struct ContractClause {
    pub span: Span,
    /// The boolean expression that must be true
    pub condition: Expr,
    /// Optional message to display on failure
    pub message: Option<String>,
}

/// Class/struct invariant - must be true after constructor and every public method.
///
/// Example:
/// ```simple
/// class BankAccount:
///     balance: i64
///
///     invariant:
///         balance >= 0
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct InvariantBlock {
    pub span: Span,
    /// Conditions that must always be true
    pub conditions: Vec<ContractClause>,
}

/// Refinement type definition (type T = Base where predicate)
///
/// Example:
/// ```simple
/// type PosI64 = i64 where self > 0
/// type NonZero = i64 where self != 0
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct RefinementType {
    pub span: Span,
    pub name: String,
    pub base_type: Type,
    /// The predicate expression (uses 'self' to refer to the value)
    pub predicate: Expr,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: struct Foo<T, U>
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub fields: Vec<Field>,
    /// Inline method definitions
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
    /// Attributes applied to the struct: #[derive(Debug)]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
    /// Struct invariant (checked after constructor and public methods)
    pub invariant: Option<InvariantBlock>,
}

impl StructDef {
    /// Check if this struct is marked with #[snapshot] attribute (CTR-062)
    /// Types with #[snapshot] have custom snapshot semantics for old() expressions.
    pub fn is_snapshot(&self) -> bool {
        self.attributes.iter().any(|attr| attr.name == "snapshot")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: class Foo<T, U>
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub fields: Vec<Field>,
    pub methods: Vec<FunctionDef>,
    pub parent: Option<String>,
    pub visibility: Visibility,
    /// Attributes applied to the class: #[deprecated]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
    /// Class invariant (checked after constructor and public methods)
    pub invariant: Option<InvariantBlock>,
}

impl ClassDef {
    /// Check if this class is marked with #[snapshot] attribute (CTR-062)
    /// Types with #[snapshot] have custom snapshot semantics for old() expressions.
    pub fn is_snapshot(&self) -> bool {
        self.attributes.iter().any(|attr| attr.name == "snapshot")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub span: Span,
    pub name: String,
    pub ty: Type,
    pub default: Option<Expr>,
    pub mutability: Mutability,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: enum Result<T, E>
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub variants: Vec<EnumVariant>,
    pub visibility: Visibility,
    /// Attributes like #[strong]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub span: Span,
    pub name: String,
    pub fields: Option<Vec<Type>>, // None = unit, Some = tuple/struct
}

/// Standalone unit type definition
/// Single-base: `unit UserId: i64 as uid`
/// Multi-base:  `unit IpAddr: str | u32 as ip` (accepts string or numeric literals)
/// Creates a newtype wrapper with literal suffix support
#[derive(Debug, Clone, PartialEq)]
pub struct UnitDef {
    pub span: Span,
    pub name: String,          // e.g., "UserId" or "IpAddr"
    pub base_types: Vec<Type>, // e.g., [i64] or [str, u32] for multi-base units
    pub suffix: String,        // e.g., "uid" or "ip" (for literals like 42_uid or "127.0.0.1"_ip)
    pub visibility: Visibility,
}

/// Unit variant in a unit family
/// e.g., `m = 1.0` or `km = 1000.0`
#[derive(Debug, Clone, PartialEq)]
pub struct UnitVariant {
    pub suffix: String, // e.g., "m", "km"
    pub factor: f64,    // conversion factor to base unit
}

/// Unit family definition: `unit length(base: f64): m = 1.0, km = 1000.0`
/// Defines a family of related units with conversion factors
#[derive(Debug, Clone, PartialEq)]
pub struct UnitFamilyDef {
    pub span: Span,
    pub name: String,    // e.g., "length"
    pub base_type: Type, // e.g., f64
    pub variants: Vec<UnitVariant>,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: trait Foo<T>
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub span: Span,
    /// Generic type parameters: impl[T]
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub target_type: Type,
    pub trait_name: Option<String>,
    pub methods: Vec<FunctionDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ActorDef {
    pub span: Span,
    pub name: String,
    pub fields: Vec<Field>,
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
}

/// Type alias definition with optional refinement predicate (CTR-020)
///
/// Simple: `type UserId = i64`
/// Refined: `type PosI64 = i64 where self > 0`
#[derive(Debug, Clone, PartialEq)]
pub struct TypeAliasDef {
    pub span: Span,
    pub name: String,
    pub ty: Type,
    pub visibility: Visibility,
    /// Refinement predicate: `where self > 0`
    /// In the predicate, `self` refers to a value of the base type
    pub where_clause: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    pub visibility: Visibility,
}

/// Macro definition: macro name!(pattern) = body
#[derive(Debug, Clone, PartialEq)]
pub struct MacroDef {
    pub span: Span,
    pub name: String,
    /// Macro patterns for matching invocations
    pub patterns: Vec<MacroPattern>,
    pub visibility: Visibility,
}

/// A single macro pattern and its expansion
#[derive(Debug, Clone, PartialEq)]
pub struct MacroPattern {
    pub span: Span,
    /// Pattern to match (e.g., parameter names, variadic patterns)
    pub params: Vec<MacroParam>,
    /// The body to expand to
    pub body: MacroBody,
}

/// A parameter in a macro pattern
#[derive(Debug, Clone, PartialEq)]
pub enum MacroParam {
    /// Simple identifier: $x
    Ident(String),
    /// Expression capture: $e:expr
    Expr(String),
    /// Type capture: $t:ty
    Type(String),
    /// Variadic capture: $(...)*
    Variadic {
        name: String,
        separator: Option<String>,
    },
    /// Literal token (must match exactly)
    Literal(String),
}

/// The body of a macro expansion
#[derive(Debug, Clone, PartialEq)]
pub enum MacroBody {
    /// Simple expression
    Expr(Box<Expr>),
    /// Block of statements
    Block(Block),
    /// Token sequence (for more complex macros)
    Tokens(Vec<MacroToken>),
}

/// A token in a macro body (for token-based expansion)
#[derive(Debug, Clone, PartialEq)]
pub enum MacroToken {
    /// Reference to captured parameter: $x
    Param(String),
    /// Stringify a captured expression: stringify!($e)
    Stringify(String),
    /// Literal token
    Literal(String),
    /// Variadic expansion: $(...)*
    Variadic {
        body: Vec<MacroToken>,
        separator: Option<String>,
    },
}

/// Macro invocation: name!(args)
#[derive(Debug, Clone, PartialEq)]
pub struct MacroInvocation {
    pub span: Span,
    pub name: String,
    pub args: Vec<MacroArg>,
}

/// An argument to a macro invocation
#[derive(Debug, Clone, PartialEq)]
pub enum MacroArg {
    Expr(Expr),
    Type(Type),
    Tokens(String), // Raw token string
}

// Statements

#[derive(Debug, Clone, PartialEq)]
pub struct LetStmt {
    pub span: Span,
    pub pattern: Pattern,
    pub ty: Option<Type>,
    pub value: Option<Expr>,
    pub mutability: Mutability,
}

/// Compile-time constant declaration
/// const PI = 3.14159
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
    Assign,    // =
    AddAssign, // +=
    SubAssign, // -=
    MulAssign, // *=
    DivAssign, // /=
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchStmt {
    pub span: Span,
    pub subject: Expr,
    pub arms: Vec<MatchArm>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub span: Span,
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForStmt {
    pub span: Span,
    pub pattern: Pattern,
    pub iterable: Expr,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub span: Span,
    /// For while-let: the pattern to match against, None for regular while
    pub let_pattern: Option<Pattern>,
    pub condition: Expr,
    pub body: Block,
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

/// Context block for DSL support
/// context expr:
///     statements
#[derive(Debug, Clone, PartialEq)]
pub struct ContextStmt {
    pub span: Span,
    pub context: Expr, // The object that becomes the implicit receiver
    pub body: Block,
}

// Types

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Simple(String),
    Generic {
        name: String,
        args: Vec<Type>,
    },
    Pointer {
        kind: PointerKind,
        inner: Box<Type>,
    },
    Tuple(Vec<Type>),
    Array {
        element: Box<Type>,
        size: Option<Box<Expr>>,
    },
    Function {
        params: Vec<Type>,
        ret: Option<Box<Type>>,
    },
    Union(Vec<Type>),
    /// Dynamic trait object: dyn Trait
    /// Allows storing any type that implements the trait
    DynTrait(String),
    Optional(Box<Type>),
    /// Constructor type: Constructor[T] or Constructor[T, (args)]
    /// Represents a constructor that produces T or a subtype of T
    Constructor {
        target: Box<Type>,
        /// Optional argument types constraint: Constructor[Widget, (str, i32)]
        args: Option<Vec<Type>>,
    },
    /// SIMD vector type: vec[N, T] where N is lane count, T is element type
    /// Supported: vec[2|4|8|16, f32|f64|i32|i64|i16|i8]
    Simd {
        lanes: u32,
        element: Box<Type>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerKind {
    Unique,    // &T
    Shared,    // *T
    Weak,      // -T
    Handle,    // +T
    Borrow,    // &T_borrow (immutable borrow)
    BorrowMut, // &mut T_borrow (mutable borrow)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    Async,
}

// Expressions

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literals
    Integer(i64),
    Float(f64),
    TypedInteger(i64, NumericSuffix), // 42i32, 100_km
    TypedFloat(f64, NumericSuffix),   // 3.14f32, 100.0_m
    String(String),
    TypedString(String, String), // "127.0.0.1"_ip - string with unit suffix
    FString(Vec<FStringPart>),   // f"hello {name}!" interpolated strings
    Bool(bool),
    Nil,
    Symbol(String),

    // Compound
    Identifier(String),
    Path(Vec<String>), // EnumName::Variant or module::item
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Argument>,
    },
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Argument>,
    },
    FieldAccess {
        receiver: Box<Expr>,
        field: String,
    },
    Index {
        receiver: Box<Expr>,
        index: Box<Expr>,
    },
    /// Tuple element access with numeric index: tuple.0, tuple.1
    TupleIndex {
        receiver: Box<Expr>,
        index: usize,
    },
    Lambda {
        params: Vec<LambdaParam>,
        body: Box<Expr>,
        move_mode: MoveMode,
    },
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        subject: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    /// List comprehension: [expr for pattern in iterable if condition]
    ListComprehension {
        expr: Box<Expr>,
        pattern: Pattern,
        iterable: Box<Expr>,
        condition: Option<Box<Expr>>,
    },
    /// Dict comprehension: {key: value for pattern in iterable if condition}
    DictComprehension {
        key: Box<Expr>,
        value: Box<Expr>,
        pattern: Pattern,
        iterable: Box<Expr>,
        condition: Option<Box<Expr>>,
    },
    /// Slice expression: items[start:end:step]
    Slice {
        receiver: Box<Expr>,
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        step: Option<Box<Expr>>,
    },
    /// Spread expression in array: *expr
    Spread(Box<Expr>),
    /// Spread expression in dict: **expr
    DictSpread(Box<Expr>),
    StructInit {
        name: String,
        fields: Vec<(String, Expr)>,
    },
    Spawn(Box<Expr>),
    Await(Box<Expr>),
    Yield(Option<Box<Expr>>), // yield or yield value
    New {
        kind: PointerKind,
        expr: Box<Expr>,
    },
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        bound: RangeBound,
    },
    /// Functional update operator: obj->method(args) desugars to obj = obj.method(args)
    FunctionalUpdate {
        target: Box<Expr>,
        method: String,
        args: Vec<Argument>,
    },
    /// Macro invocation: name!(args)
    MacroInvocation {
        name: String,
        args: Vec<MacroArg>,
    },
    /// Try operator: expr? - unwrap Ok or early return Err
    Try(Box<Expr>),

    // Contract-specific expressions (LLM-friendly feature #400)
    /// Result identifier in ensures block - refers to return value
    ContractResult,
    /// old(expr) in ensures block - refers to value before function execution
    ContractOld(Box<Expr>),

    /// Do block - a sequence of statements that evaluate to () (unit)
    /// Used for colon-block syntax in BDD DSL: `describe "name": body`
    DoBlock(Vec<Node>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    pub name: Option<String>, // for named arguments
    pub value: Expr,
}

/// Part of an f-string (interpolated string)
#[derive(Debug, Clone, PartialEq)]
pub enum FStringPart {
    Literal(String),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaParam {
    pub name: String,
    pub ty: Option<Type>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    FloorDiv,
    // Comparison
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    // Logical
    And,
    Or,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    // Other
    Is,
    In,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,    // -
    Not,    // not
    BitNot, // ~
    Ref,    // & (immutable borrow)
    RefMut, // &mut (mutable borrow)
    Deref,  // *
}

// Patterns

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Identifier(String),
    MutIdentifier(String),
    Literal(Box<Expr>),
    Tuple(Vec<Pattern>),
    Array(Vec<Pattern>),
    Struct {
        name: String,
        fields: Vec<(String, Pattern)>,
    },
    Enum {
        name: String,
        variant: String,
        payload: Option<Vec<Pattern>>,
    },
    Or(Vec<Pattern>),
    Typed {
        pattern: Box<Pattern>,
        ty: Type,
    },
    /// Range pattern: start..end (exclusive) or start..=end (inclusive)
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    Rest, // ...
}

// Module level

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub name: Option<String>,
    pub items: Vec<Node>,
}

//==============================================================================
// Module System (Features #104-111)
//==============================================================================

/// Module path for imports: crate.sys.http.router
#[derive(Debug, Clone, PartialEq)]
pub struct ModulePath {
    /// Path segments separated by dots: ["crate", "sys", "http", "router"]
    pub segments: Vec<String>,
}

impl ModulePath {
    pub fn new(segments: Vec<String>) -> Self {
        Self { segments }
    }
}

/// Import target: what to import from a module
#[derive(Debug, Clone, PartialEq)]
pub enum ImportTarget {
    /// Single item: use crate.core.Option
    Single(String),
    /// Aliased import: use crate.core.Option as Opt
    Aliased { name: String, alias: String },
    /// Group import: use crate.core.{Option, Result, Vec}
    Group(Vec<ImportTarget>),
    /// Glob import: use crate.core.*
    Glob,
}

/// Module declaration: mod name or pub mod name
/// #[no_gc]
/// pub mod router
#[derive(Debug, Clone, PartialEq)]
pub struct ModDecl {
    pub span: Span,
    pub name: String,
    pub visibility: Visibility,
    pub attributes: Vec<Attribute>,
}

/// Use statement: use module.path.{items}
/// use crate.core.Option
/// use crate.core.{Option, Result}
/// use crate.core.*
/// use crate.core.Option as Opt
#[derive(Debug, Clone, PartialEq)]
pub struct UseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
}

/// Common use statement: common use module.path.*
/// Directory prelude - applies to all files in directory
/// common use crate.core.base.*
#[derive(Debug, Clone, PartialEq)]
pub struct CommonUseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
}

/// Export use statement: export use module.path.{items}
/// Re-export from child modules
/// export use router.Router
/// export use router.{Client, Request}
/// export use router.*
#[derive(Debug, Clone, PartialEq)]
pub struct ExportUseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
}

/// Auto import statement: auto import module.macro_name
/// Makes macros available in glob imports
/// auto import router.route
#[derive(Debug, Clone, PartialEq)]
pub struct AutoImportStmt {
    pub span: Span,
    pub path: ModulePath,
    pub macro_name: String,
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
