//! Core AST node types including the main Node enum and common utilities

use super::super::aop::*;
use super::super::enums::*;
use crate::token::{NumericSuffix, Span};
// Import from sibling modules
use super::definitions::*;
use super::modules::*;
use super::statements::*;
// Effects and capabilities are in effects.rs
pub use super::effects::{Capability, Effect};

/// All AST node types
#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    // Definitions
    Function(FunctionDef),
    Struct(StructDef),
    Bitfield(BitfieldDef),
    Class(ClassDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplBlock),
    InterfaceBinding(InterfaceBinding),
    Mixin(MixinDef),
    Actor(ActorDef),
    TypeAlias(TypeAliasDef),
    Extern(ExternDef),
    Macro(MacroDef),
    Unit(UnitDef),
    UnitFamily(UnitFamilyDef),
    CompoundUnit(CompoundUnitDef),
    HandlePool(HandlePoolDef),

    // Module system (Features #104-111)
    ModDecl(ModDecl),
    UseStmt(UseStmt),
    CommonUseStmt(CommonUseStmt),
    ExportUseStmt(ExportUseStmt),
    AutoImportStmt(AutoImportStmt),
    RequiresCapabilities(RequiresCapabilitiesStmt),

    // Gherkin-style system test DSL (#606-610)
    // NOTE: Gherkin syntax is now transformed to regular Simple AST:
    // - feature("name", do_block) - function call
    // - scenario("name", do_block) - function call
    // - given/when/then("pattern", do_block) - function calls
    // - examples("name", [...]) - function call with array
    // No special AST nodes needed - uses existing Expr::Call and Expr::DoBlock

    // AOP & Unified Predicates (#1000-1050)
    AopAdvice(AopAdvice),
    DiBinding(DiBinding),
    ArchitectureRule(ArchitectureRule),
    MockDecl(MockDecl),

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

/// Decorator applied to a function: @decorator or @decorator(args)
/// Args support named arguments: @bounds(default="return", strict=true)
#[derive(Debug, Clone, PartialEq)]
pub struct Decorator {
    pub span: Span,
    pub name: Expr,                  // The decorator expression (e.g., Identifier or Call)
    pub args: Option<Vec<Argument>>, // Arguments if @decorator(args), supports named args
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
///
/// Supports interpolation syntax: `${examples name}` embeds an examples table.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct DocComment {
    /// The documentation text (used directly as API description)
    pub content: String,
}

/// Part of a doc comment - either literal text or an interpolation reference.
#[derive(Debug, Clone, PartialEq)]
pub enum DocPart {
    /// Literal text
    Text(String),
    /// Interpolation: `${examples name}` -> ExamplesRef(name)
    ExamplesRef(String),
}

impl DocComment {
    /// Create a DocComment from raw content.
    /// The content is used directly as the API description.
    pub fn new(content: String) -> Self {
        DocComment {
            content: content.trim().to_string(),
        }
    }

    /// Parse doc comment content into parts, extracting `${examples name}` interpolations.
    /// Returns a list of DocPart (text and examples references).
    pub fn parse_parts(&self) -> Vec<DocPart> {
        let mut parts = Vec::new();
        let mut remaining = self.content.as_str();

        while let Some(start) = remaining.find("${examples ") {
            // Add text before the interpolation
            if start > 0 {
                parts.push(DocPart::Text(remaining[..start].to_string()));
            }

            // Find the end of the interpolation
            let after_start = &remaining[start + 11..]; // Skip "${examples "
            if let Some(end) = after_start.find('}') {
                let name = after_start[..end].trim().to_string();
                parts.push(DocPart::ExamplesRef(name));
                remaining = &after_start[end + 1..];
            } else {
                // Unclosed interpolation - treat as text
                parts.push(DocPart::Text(remaining[start..].to_string()));
                remaining = "";
            }
        }

        // Add remaining text
        if !remaining.is_empty() {
            parts.push(DocPart::Text(remaining.to_string()));
        }

        parts
    }

    /// Check if this doc comment contains any interpolations.
    pub fn has_interpolations(&self) -> bool {
        self.content.contains("${examples ")
    }

    /// Get all examples names referenced in this doc comment.
    pub fn examples_refs(&self) -> Vec<String> {
        self.parse_parts()
            .into_iter()
            .filter_map(|part| {
                if let DocPart::ExamplesRef(name) = part {
                    Some(name)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Expand interpolations using a resolver function.
    /// The resolver takes an examples name and returns the table content as a string.
    pub fn expand<F>(&self, resolver: F) -> String
    where
        F: Fn(&str) -> Option<String>,
    {
        let parts = self.parse_parts();
        let mut result = String::new();

        for part in parts {
            match part {
                DocPart::Text(text) => result.push_str(&text),
                DocPart::ExamplesRef(name) => {
                    if let Some(table) = resolver(&name) {
                        result.push_str(&table);
                    } else {
                        // Keep original if not found
                        result.push_str(&format!("${{examples {}}}", name));
                    }
                }
            }
        }

        result
    }
}

/// A single where bound: `T: Trait1 + Trait2`
///
/// Example:
/// ```simple
/// fn make[T]() -> T where T: Clone + Default:
///     return T.default()
/// fn sum[T]() -> T where T: Add<Output=T>:
///     ...
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct WhereBound {
    pub span: Span,
    /// The type parameter being constrained (e.g., "T")
    pub type_param: String,
    /// The trait bounds as full type expressions
    /// Can be simple: `Clone`, `Default`
    /// Or parameterized: `Add<Output=T>`, `Iterator<Item=String>`
    pub bounds: Vec<Type>,
    /// Negative bounds: bounds that must NOT be implemented (#1151)
    /// Example: T: !Clone means T must NOT implement Clone
    pub negative_bounds: Vec<Type>,
}

/// A where clause containing multiple bounds
pub type WhereClause = Vec<WhereBound>;

/// A generic parameter: either a type parameter or a const parameter
///
/// Example:
/// ```simple
/// struct Array[T, const N: usize]:  // T is TypeParam, N is ConstParam
///     data: T
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum GenericParam {
    /// Type parameter: T, U, etc.
    /// Can optionally have trait bounds: T: Display, I: Iterator
    /// Can optionally have default type: Rhs = Self
    Type {
        name: String,
        bounds: Vec<String>,
        default: Option<Type>,
    },
    /// Const parameter: const N: usize
    Const { name: String, ty: Type },
}

impl GenericParam {
    /// Get the name of the parameter
    pub fn name(&self) -> &str {
        match self {
            GenericParam::Type { name, .. } => name,
            GenericParam::Const { name, .. } => name,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub default: Option<Expr>,
    pub mutability: Mutability,
    /// Per-parameter DI injection flag (#1013)
    pub inject: bool,
    /// Variadic parameter flag (e.g., items: T...)
    pub variadic: bool,
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

// Types

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Simple(String),
    Generic {
        name: String,
        args: Vec<Type>,
    },
    /// Reference capability wrapper (mut T, iso T)
    /// Tracks what operations are permitted on a reference
    Capability {
        capability: super::super::enums::ReferenceCapability,
        inner: Box<Type>,
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
    /// Unit type with representation constraint: `_cm:u12` or `_cm where range: 0..100`
    /// Used in bitfields and for compact storage with type safety
    UnitWithRepr {
        name: String,
        repr: Option<ReprType>,
        constraints: UnitReprConstraints,
    },
    /// Self type: `self` used as return type in methods
    /// Resolved to the enclosing type during semantic analysis
    /// Enables fluent APIs: fn increment() -> self
    SelfType,
    /// Associated type binding in trait bounds: Iterator<Item=T>, Ord<Output=Bool>
    /// Used in where clauses and trait bounds to constrain associated types
    TypeBinding {
        /// The associated type name (e.g., "Item")
        name: String,
        /// The type it's bound to (e.g., T or String)
        value: Box<Type>,
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
    RawConst,  // *const T (FFI const pointer)
    RawMut,    // *mut T (FFI mutable pointer)
}

/// Function effect annotations for capability-based effect tracking.
///
/// Effects declare what side effects a function may perform.
/// Functions without effect annotations are unrestricted (can do anything).
/// Functions with @pure cannot perform any I/O, network, or filesystem operations.
///
/// Example:
/// ```simple
/// @pure
/// fn add(x: i64, y: i64) -> i64:
///     return x + y
///
/// @io @net
/// fn fetch_and_log(url: str):
///     let data = http_get(url)
///     print(data)
/// ```
// Effect and Capability types are in effects.rs module

// Expressions

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literals
    Integer(i64),
    Float(f64),
    TypedInteger(i64, NumericSuffix), // 42i32, 100_km
    TypedFloat(f64, NumericSuffix),   // 3.15f32, 100.0_m
    String(String),
    TypedString(String, String), // "127.0.0.1"_ip - string with unit suffix
    FString(Vec<FStringPart>),   // f"hello {name}!" interpolated strings
    Bool(bool),
    Nil,
    Symbol(String),

    /// i18n named string: Name_"default text"
    I18nString {
        name: String,
        default_text: String,
    },
    /// i18n string with template: Name_"Hello {user}!"{user: name}
    I18nTemplate {
        name: String,
        parts: Vec<FStringPart>, // Reuse existing FStringPart
        args: Vec<(String, Expr)>,
    },
    /// Reference to i18n string by name only: print(Login_failed)
    I18nRef(String),

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
        /// Capture all immutables (from \*: syntax)
        capture_all: bool,
    },
    If {
        let_pattern: Option<Pattern>,
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
    /// Array repetition: [value; count] creates array with `count` copies of `value`
    /// Example: [0; 10] creates [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ArrayRepeat {
        value: Box<Expr>,
        count: Box<Expr>,
    },
    /// SIMD vector literal: vec[1.0, 2.0, 3.0, 4.0]
    VecLiteral(Vec<Expr>),
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
    /// Go-style thread spawn:
    /// - `go(x, y) \a, b: expr` - pass x, y as arguments to parameters a, b
    /// - `go(x, y) \ *: expr` or `go(x, y) \: expr` - capture x, y and use in expr
    /// - `go() \ *: expr`, `go() \: expr`, or `go \ *:` - capture all immutables
    Go {
        /// Arguments to pass to thread
        /// Empty vec means capture all immutables in scope
        args: Vec<Expr>,
        /// Parameters received by thread lambda
        /// Empty vec means capture form (no params, uses captures)
        params: Vec<String>,
        /// Body expression to execute in thread
        body: Box<Expr>,
    },
    Await(Box<Expr>),
    Yield(Option<Box<Expr>>), // yield or yield value
    New {
        kind: PointerKind,
        expr: Box<Expr>,
    },
    /// Type cast expression: expr as Type
    Cast {
        expr: Box<Expr>,
        target_type: Type,
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

    // Simple Math literals (#1910-#1969)
    /// Grid literal: grid device="cuda": | row | row |
    GridLiteral {
        rows: Vec<Vec<Box<Expr>>>,
        device: Option<String>,
    },
    /// Tensor literal: tensor K: Float [d=2, h=3] ...
    TensorLiteral {
        dtype: String,
        dims: Vec<(String, i64)>,
        mode: Box<TensorMode>,
        device: Option<String>,
    },

    /// Custom block expression: m{...}, sh{...}, sql{...}, re{...}, etc.
    /// DSL embedding with typed result based on block kind.
    BlockExpr {
        /// Block kind: "m", "sh", "sql", "re", "md", "html", "graph", "img"
        kind: String,
        /// Raw payload content (parsed by block-specific handler)
        payload: String,
    },
}

/// Tensor rendering mode for N-dimensional tensors (#1910-#1969)
#[derive(Debug, Clone, PartialEq)]
pub enum TensorMode {
    /// Slice mode: explicit slices with grid rows
    Slice(Vec<TensorSlice>),
    /// Flat mode: sparse representation with default value
    Flat {
        default: Option<Box<Expr>>,
        values: Vec<Vec<Box<Expr>>>,
    },
}

/// A single slice in tensor slice mode
#[derive(Debug, Clone, PartialEq)]
pub struct TensorSlice {
    pub dim_name: String,
    pub dim_value: i64,
    pub content: TensorSliceContent,
}

/// Content of a tensor slice - can be nested slices or grid rows
#[derive(Debug, Clone, PartialEq)]
pub enum TensorSliceContent {
    NestedSlices(Vec<TensorSlice>),
    GridRows(Vec<Vec<Box<Expr>>>),
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
    MatMul, // @ operator for matrix multiplication (Simple Math #1930-#1939)
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
    AndSuspend, // and~ (suspending AND - awaits RHS)
    OrSuspend,  // or~ (suspending OR - awaits RHS)
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
    Neg,         // -
    Not,         // not
    BitNot,      // ~
    Ref,         // & (immutable borrow)
    RefMut,      // &mut (mutable borrow)
    Deref,       // *
    ChannelRecv, // <- (channel receive)
    Move,        // move (explicit ownership transfer)
}

// Patterns

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Identifier(String),
    MutIdentifier(String),
    MoveIdentifier(String), // move name - transfers ownership during pattern matching
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

impl Default for Module {
    fn default() -> Self {
        Self {
            name: None,
            items: Vec::new(),
        }
    }
}

/// An argument to a macro invocation
#[derive(Debug, Clone, PartialEq)]
pub enum MacroArg {
    Expr(Expr),
}

/// Associated type declaration in a trait
/// Example: `type Item` or `type Item: Clone` or `type Item = i64`
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeDef {
    pub span: Span,
    pub name: String,
    /// Optional trait bounds: `type Item: Clone + Default`
    pub bounds: Vec<String>,
    /// Optional default type: `type Item = i64`
    pub default: Option<Type>,
}

/// Associated type implementation in an impl block
/// Example: `type Item = i64`
#[derive(Debug, Clone, PartialEq)]
pub struct AssociatedTypeImpl {
    pub span: Span,
    pub name: String,
    pub ty: Type,
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

/// A field in an enum variant, can be named or positional
/// Named: `RGB(r: Int, g: Int, b: Int)` - name is Some("r"), Some("g"), Some("b")
/// Positional: `RGB(Int, Int, Int)` - name is None for all fields
#[derive(Debug, Clone, PartialEq)]
pub struct EnumField {
    pub name: Option<String>, // None for positional, Some("name") for named
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumVariant {
    pub span: Span,
    pub name: String,
    pub fields: Option<Vec<EnumField>>, // None = unit, Some = tuple/struct
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub span: Span,
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Block,
}
