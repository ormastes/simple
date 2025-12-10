use crate::token::{NumericSuffix, Span};

//==============================================================================
// Visibility and Mutability (for formal verification)
//==============================================================================
// These enums replace boolean flags to make the semantics explicit.
// This simplifies formal verification by making invalid states unrepresentable.

/// Visibility of a declaration.
///
/// Lean equivalent:
/// ```lean
/// inductive Visibility
///   | public
///   | private
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Visibility {
    /// Publicly accessible
    Public,
    /// Private to the module (default)
    #[default]
    Private,
}

impl Visibility {
    /// Check if this is public visibility
    pub fn is_public(&self) -> bool {
        matches!(self, Visibility::Public)
    }
}

/// Mutability of a binding or field.
///
/// Lean equivalent:
/// ```lean
/// inductive Mutability
///   | mutable
///   | immutable
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Mutability {
    /// Can be modified
    Mutable,
    /// Cannot be modified (default)
    #[default]
    Immutable,
}

impl Mutability {
    /// Check if this is mutable
    pub fn is_mutable(&self) -> bool {
        matches!(self, Mutability::Mutable)
    }
}

/// Range bound type - whether the end bound is inclusive or exclusive.
///
/// Lean equivalent:
/// ```lean
/// inductive RangeBound
///   | inclusive  -- a..=b includes b
///   | exclusive  -- a..b excludes b
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RangeBound {
    /// Inclusive bound (a..=b includes b)
    Inclusive,
    /// Exclusive bound (a..b excludes b, default)
    #[default]
    Exclusive,
}

impl RangeBound {
    /// Check if this is inclusive
    pub fn is_inclusive(&self) -> bool {
        matches!(self, RangeBound::Inclusive)
    }

    /// Check if this is exclusive
    pub fn is_exclusive(&self) -> bool {
        matches!(self, RangeBound::Exclusive)
    }
}

/// Self-binding mode for method calls.
/// Distinguishes whether `self` should be explicitly bound in parameter evaluation.
///
/// Lean equivalent:
/// ```lean
/// inductive SelfMode
///   | includeSelf  -- bind self from parameters
///   | skipSelf     -- self is already bound
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SelfMode {
    /// Include self in parameter binding (for constructors, free functions)
    #[default]
    IncludeSelf,
    /// Skip self in parameter binding (self already bound to receiver)
    SkipSelf,
}

impl SelfMode {
    /// Check if self should be skipped
    pub fn should_skip_self(&self) -> bool {
        matches!(self, SelfMode::SkipSelf)
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: fn foo<T, U>(...)
    pub generic_params: Vec<String>,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    pub body: Block,
    pub visibility: Visibility,
    pub effect: Option<Effect>,
    /// Decorators applied to the function: @decorator
    pub decorators: Vec<Decorator>,
    /// Attributes applied to the function: #[inline], #[deprecated]
    pub attributes: Vec<Attribute>,
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

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: struct Foo<T, U>
    pub generic_params: Vec<String>,
    pub fields: Vec<Field>,
    pub visibility: Visibility,
    /// Attributes applied to the struct: #[derive(Debug)]
    pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClassDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: class Foo<T, U>
    pub generic_params: Vec<String>,
    pub fields: Vec<Field>,
    pub methods: Vec<FunctionDef>,
    pub parent: Option<String>,
    pub visibility: Visibility,
    /// Attributes applied to the class: #[deprecated]
    pub attributes: Vec<Attribute>,
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
    pub variants: Vec<EnumVariant>,
    pub visibility: Visibility,
    /// Attributes like #[strong]
    pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub span: Span,
    pub name: String,
    pub fields: Option<Vec<Type>>, // None = unit, Some = tuple/struct
}

/// Standalone unit type definition: `unit UserId: i64 as uid`
/// Creates a newtype wrapper with literal suffix support
#[derive(Debug, Clone, PartialEq)]
pub struct UnitDef {
    pub span: Span,
    pub name: String,    // e.g., "UserId"
    pub base_type: Type, // e.g., i64
    pub suffix: String,  // e.g., "uid" (for literals like 42_uid)
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: trait Foo<T>
    pub generic_params: Vec<String>,
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub span: Span,
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeAliasDef {
    pub span: Span,
    pub name: String,
    pub ty: Type,
    pub visibility: Visibility,
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
    Optional(Box<Type>),
    /// Constructor type: Constructor[T] or Constructor[T, (args)]
    /// Represents a constructor that produces T or a subtype of T
    Constructor {
        target: Box<Type>,
        /// Optional argument types constraint: Constructor[Widget, (str, i32)]
        args: Option<Vec<Type>>,
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
    FString(Vec<FStringPart>), // f"hello {name}!" interpolated strings
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
    Lambda {
        params: Vec<LambdaParam>,
        body: Box<Expr>,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_integer() {
        let expr = Expr::Integer(42);
        assert_eq!(expr, Expr::Integer(42));
    }

    #[test]
    fn test_binary_expr() {
        let expr = Expr::Binary {
            op: BinOp::Add,
            left: Box::new(Expr::Integer(1)),
            right: Box::new(Expr::Integer(2)),
        };
        if let Expr::Binary { op, .. } = expr {
            assert_eq!(op, BinOp::Add);
        } else {
            panic!("Expected Binary expression");
        }
    }

    #[test]
    fn test_function_def() {
        let func = FunctionDef {
            span: Span::new(0, 10, 1, 1),
            name: "add".to_string(),
            generic_params: vec![],
            params: vec![Parameter {
                span: Span::new(4, 5, 1, 5),
                name: "a".to_string(),
                ty: Some(Type::Simple("Int".to_string())),
                default: None,
                mutability: Mutability::Immutable,
            }],
            return_type: Some(Type::Simple("Int".to_string())),
            body: Block::default(),
            visibility: Visibility::Private,
            effect: None,
            decorators: vec![],
            attributes: vec![],
        };
        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 1);
    }

    #[test]
    fn test_generic_function_def() {
        let func = FunctionDef {
            span: Span::new(0, 20, 1, 1),
            name: "identity".to_string(),
            generic_params: vec!["T".to_string()],
            params: vec![Parameter {
                span: Span::new(10, 11, 1, 11),
                name: "x".to_string(),
                ty: Some(Type::Simple("T".to_string())),
                default: None,
                mutability: Mutability::Immutable,
            }],
            return_type: Some(Type::Simple("T".to_string())),
            body: Block::default(),
            visibility: Visibility::Private,
            effect: None,
            decorators: vec![],
            attributes: vec![],
        };
        assert_eq!(func.name, "identity");
        assert_eq!(func.generic_params, vec!["T"]);
    }

    #[test]
    fn test_generic_struct_def() {
        let s = StructDef {
            span: Span::new(0, 30, 1, 1),
            name: "Box".to_string(),
            generic_params: vec!["T".to_string()],
            fields: vec![Field {
                span: Span::new(10, 20, 2, 5),
                name: "value".to_string(),
                ty: Type::Simple("T".to_string()),
                default: None,
                mutability: Mutability::Immutable,
                visibility: Visibility::Private,
            }],
            visibility: Visibility::Private,
            attributes: vec![],
        };
        assert_eq!(s.name, "Box");
        assert_eq!(s.generic_params, vec!["T"]);
    }
}
