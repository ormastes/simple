use crate::token::Span;

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
    Expression(Expr),
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
    pub is_public: bool,
    pub effect: Option<Effect>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub default: Option<Expr>,
    pub is_mutable: bool,
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
    pub is_public: bool,
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
    pub is_public: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub span: Span,
    pub name: String,
    pub ty: Type,
    pub default: Option<Expr>,
    pub is_mutable: bool,
    pub is_public: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: enum Result<T, E>
    pub generic_params: Vec<String>,
    pub variants: Vec<EnumVariant>,
    pub is_public: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub span: Span,
    pub name: String,
    pub fields: Option<Vec<Type>>,  // None = unit, Some = tuple/struct
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: trait Foo<T>
    pub generic_params: Vec<String>,
    pub methods: Vec<FunctionDef>,
    pub is_public: bool,
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
    pub is_public: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeAliasDef {
    pub span: Span,
    pub name: String,
    pub ty: Type,
    pub is_public: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    pub is_public: bool,
}

/// Macro definition: macro name!(pattern) = body
#[derive(Debug, Clone, PartialEq)]
pub struct MacroDef {
    pub span: Span,
    pub name: String,
    /// Macro patterns for matching invocations
    pub patterns: Vec<MacroPattern>,
    pub is_public: bool,
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
    Variadic { name: String, separator: Option<String> },
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
    Variadic { body: Vec<MacroToken>, separator: Option<String> },
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
    pub is_mutable: bool,
}

/// Compile-time constant declaration
/// const PI = 3.14159
/// const MAX_SIZE: i64 = 100
#[derive(Debug, Clone, PartialEq)]
pub struct ConstStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,  // Required - must be evaluable at compile time
    pub is_public: bool,
}

/// Static variable declaration (global, initialized once)
/// static counter = 0
/// static mut config = {}
#[derive(Debug, Clone, PartialEq)]
pub struct StaticStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,  // Required
    pub is_mutable: bool,
    pub is_public: bool,
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
    Assign,     // =
    AddAssign,  // +=
    SubAssign,  // -=
    MulAssign,  // *=
    DivAssign,  // /=
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub span: Span,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub span: Span,
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
    pub context: Expr,  // The object that becomes the implicit receiver
    pub body: Block,
}

// Types

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Simple(String),
    Generic { name: String, args: Vec<Type> },
    Pointer { kind: PointerKind, inner: Box<Type> },
    Tuple(Vec<Type>),
    Array { element: Box<Type>, size: Option<Box<Expr>> },
    Function { params: Vec<Type>, ret: Option<Box<Type>> },
    Union(Vec<Type>),
    Optional(Box<Type>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerKind {
    Unique,   // &T
    Shared,   // *T
    Weak,     // -T
    Handle,   // +T
    Borrow,      // &T_borrow (immutable borrow)
    BorrowMut,   // &mut T_borrow (mutable borrow)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    Async,
    Waitless,
}

// Expressions

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    FString(Vec<FStringPart>),  // f"hello {name}!" interpolated strings
    Bool(bool),
    Nil,
    Symbol(String),

    // Compound
    Identifier(String),
    Path(Vec<String>),  // EnumName::Variant or module::item
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr> },
    Unary { op: UnaryOp, operand: Box<Expr> },
    Call { callee: Box<Expr>, args: Vec<Argument> },
    MethodCall { receiver: Box<Expr>, method: String, args: Vec<Argument> },
    FieldAccess { receiver: Box<Expr>, field: String },
    Index { receiver: Box<Expr>, index: Box<Expr> },
    Lambda { params: Vec<LambdaParam>, body: Box<Expr> },
    If { condition: Box<Expr>, then_branch: Box<Expr>, else_branch: Option<Box<Expr>> },
    Match { subject: Box<Expr>, arms: Vec<MatchArm> },
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    StructInit { name: String, fields: Vec<(String, Expr)> },
    Spawn(Box<Expr>),
    Await(Box<Expr>),
    Yield(Option<Box<Expr>>),  // yield or yield value
    New { kind: PointerKind, expr: Box<Expr> },
    Range { start: Option<Box<Expr>>, end: Option<Box<Expr>>, inclusive: bool },
    /// Functional update operator: obj->method(args) desugars to obj = obj.method(args)
    FunctionalUpdate { target: Box<Expr>, method: String, args: Vec<Argument> },
    /// Macro invocation: name!(args)
    MacroInvocation { name: String, args: Vec<MacroArg> },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    pub name: Option<String>,  // for named arguments
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
    Add, Sub, Mul, Div, Mod, Pow, FloorDiv,
    // Comparison
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    // Logical
    And, Or,
    // Bitwise
    BitAnd, BitOr, BitXor, ShiftLeft, ShiftRight,
    // Other
    Is, In,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,      // -
    Not,      // not
    BitNot,   // ~
    Ref,      // & (immutable borrow)
    RefMut,   // &mut (mutable borrow)
    Deref,    // *
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
    Struct { name: String, fields: Vec<(String, Pattern)> },
    Enum { name: String, variant: String, payload: Option<Vec<Pattern>> },
    Or(Vec<Pattern>),
    Typed { pattern: Box<Pattern>, ty: Type },
    Rest,  // ...
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
            params: vec![
                Parameter {
                    span: Span::new(4, 5, 1, 5),
                    name: "a".to_string(),
                    ty: Some(Type::Simple("Int".to_string())),
                    default: None,
                    is_mutable: false,
                },
            ],
            return_type: Some(Type::Simple("Int".to_string())),
            body: Block::default(),
            is_public: false,
            effect: None,
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
            params: vec![
                Parameter {
                    span: Span::new(10, 11, 1, 11),
                    name: "x".to_string(),
                    ty: Some(Type::Simple("T".to_string())),
                    default: None,
                    is_mutable: false,
                },
            ],
            return_type: Some(Type::Simple("T".to_string())),
            body: Block::default(),
            is_public: false,
            effect: None,
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
            fields: vec![
                Field {
                    span: Span::new(10, 20, 2, 5),
                    name: "value".to_string(),
                    ty: Type::Simple("T".to_string()),
                    default: None,
                    is_mutable: false,
                    is_public: false,
                },
            ],
            is_public: false,
        };
        assert_eq!(s.name, "Box");
        assert_eq!(s.generic_params, vec!["T"]);
    }
}
