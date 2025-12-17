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
    CompoundUnit(CompoundUnitDef),
    HandlePool(HandlePoolDef),

    // Module system (Features #104-111)
    ModDecl(ModDecl),
    UseStmt(UseStmt),
    CommonUseStmt(CommonUseStmt),
    ExportUseStmt(ExportUseStmt),
    AutoImportStmt(AutoImportStmt),
    RequiresCapabilities(RequiresCapabilitiesStmt),

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
    /// Effect annotations: @pure, @io, @net, @fs, @unsafe, @async
    /// Multiple effects can be stacked: @io @net fn fetch()
    /// Empty = unrestricted (can do anything)
    pub effects: Vec<Effect>,
    /// Decorators applied to the function: @decorator (non-effect decorators)
    pub decorators: Vec<Decorator>,
    /// Attributes applied to the function: #[inline], #[deprecated]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
    /// Contract specification (requires/ensures)
    pub contract: Option<ContractBlock>,
    /// Whether this is an abstract method (trait method without body)
    pub is_abstract: bool,
    /// Bounds block for @simd kernels (trailing bounds: clause)
    pub bounds_block: Option<BoundsBlock>,
}

impl FunctionDef {
    /// Check if this function is marked as pure via @pure effect or #[pure] attribute.
    /// Pure functions cannot perform I/O, network, filesystem, or GC operations.
    /// Pure functions can be called from contract expressions (CTR-031).
    pub fn is_pure(&self) -> bool {
        self.effects.contains(&Effect::Pure)
            || self.attributes.iter().any(|attr| attr.name == "pure")
    }

    /// Check if this function has the @async effect.
    /// Async functions cannot call blocking operations.
    pub fn is_async(&self) -> bool {
        self.effects.contains(&Effect::Async)
    }

    /// Check if this function has the @io effect.
    /// Functions with @io can perform console I/O operations.
    pub fn has_io(&self) -> bool {
        self.effects.contains(&Effect::Io)
    }

    /// Check if this function has the @net effect.
    /// Functions with @net can perform network operations.
    pub fn has_net(&self) -> bool {
        self.effects.contains(&Effect::Net)
    }

    /// Check if this function has the @fs effect.
    /// Functions with @fs can perform filesystem operations.
    pub fn has_fs(&self) -> bool {
        self.effects.contains(&Effect::Fs)
    }

    /// Check if this function has the @unsafe effect.
    /// Functions with @unsafe can perform unchecked operations.
    pub fn has_unsafe(&self) -> bool {
        self.effects.contains(&Effect::Unsafe)
    }

    /// Check if this function has any effect annotations.
    /// Functions without effects are unrestricted.
    pub fn has_effects(&self) -> bool {
        !self.effects.is_empty()
    }

    /// Check if this function has the @simd decorator.
    pub fn has_simd_decorator(&self) -> bool {
        self.decorators.iter().any(|d| {
            matches!(&d.name, Expr::Identifier(name) if name == "simd")
        })
    }
}

// =============================================================================
// Bounds block types for @simd kernels
// =============================================================================

/// SIMD kernel bounds specification
/// Trailing block after @simd function defining bounds handling
#[derive(Debug, Clone, PartialEq)]
pub struct BoundsBlock {
    pub span: Span,
    /// Bounds cases with patterns and handlers
    pub cases: Vec<BoundsCase>,
}

/// Single case in a bounds: block
#[derive(Debug, Clone, PartialEq)]
pub struct BoundsCase {
    pub span: Span,
    /// Pattern condition (can be boolean composition)
    pub pattern: BoundsPattern,
    /// Handler body
    pub body: Block,
}

/// Bounds pattern - boolean composition of bounds atoms
#[derive(Debug, Clone, PartialEq)]
pub enum BoundsPattern {
    /// Single bounds atom: _.var.kind
    Atom(BoundsAtom),
    /// Boolean AND: pattern && pattern
    And(Box<BoundsPattern>, Box<BoundsPattern>),
    /// Boolean OR: pattern || pattern
    Or(Box<BoundsPattern>, Box<BoundsPattern>),
    /// Parenthesized: (pattern)
    Paren(Box<BoundsPattern>),
    /// Default catch-all: _
    Default,
}

/// Bounds atom: _.<variable>.<kind>
#[derive(Debug, Clone, PartialEq)]
pub struct BoundsAtom {
    pub span: Span,
    /// Variable name being indexed (e.g., "out", "a")
    pub variable: String,
    /// Bounds kind: over or under
    pub kind: BoundsKind,
}

/// Kind of bounds event
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundsKind {
    /// index >= length (overflow)
    Over,
    /// index < 0 (underflow)
    Under,
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

/// Handle pool declaration for a type
/// ```simple
/// handle_pool Enemy:
///     capacity: 1024
/// ```
/// Declares a global handle pool for allocating handles to a specific type.
/// Required before using `new+ T(...)` syntax.
#[derive(Debug, Clone, PartialEq)]
pub struct HandlePoolDef {
    pub span: Span,
    pub type_name: String,         // The type this pool manages (e.g., "Enemy")
    pub capacity: Option<u64>,      // Optional initial capacity
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
    /// Optional arithmetic rules block
    pub arithmetic: Option<UnitArithmetic>,
}

/// Arithmetic rules for a unit family
/// Defines allowed operations like `allow add(length) -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct UnitArithmetic {
    pub binary_rules: Vec<BinaryArithmeticRule>,
    pub unary_rules: Vec<UnaryArithmeticRule>,
    pub custom_fns: Vec<FunctionDef>,
    /// Allowed representations: repr: u8, u12, i16, f32, ...
    pub allowed_reprs: Vec<ReprType>,
}

/// Representation type for bit-limited units
/// Examples: u8, u12, i16, i24, f32, f64
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReprType {
    pub signed: bool,      // true for i/f, false for u
    pub bits: u8,          // bit width (8, 12, 16, 24, 32, 64)
    pub is_float: bool,    // true for f16, f32, f64
}

impl ReprType {
    pub fn new(signed: bool, bits: u8, is_float: bool) -> Self {
        Self { signed, bits, is_float }
    }

    /// Parse from string like "u8", "i12", "f32"
    pub fn from_str(s: &str) -> Option<Self> {
        if s.is_empty() {
            return None;
        }
        let (prefix, rest) = s.split_at(1);
        let bits: u8 = rest.parse().ok()?;
        match prefix {
            "u" => Some(Self::new(false, bits, false)),
            "i" => Some(Self::new(true, bits, false)),
            "f" => Some(Self::new(true, bits, true)),
            _ => None,
        }
    }

    /// Convert to string like "u8", "i12", "f32"
    pub fn to_string(&self) -> String {
        let prefix = if self.is_float {
            "f"
        } else if self.signed {
            "i"
        } else {
            "u"
        };
        format!("{}{}", prefix, self.bits)
    }
}

/// Overflow behavior for bit-limited units
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OverflowBehavior {
    /// Default: panic in debug, undefined in release
    #[default]
    Default,
    /// Always panic on overflow
    Checked,
    /// Clamp to min/max
    Saturate,
    /// Modular arithmetic (wrap around)
    Wrap,
}

/// Constraints for unit type with representation
/// Used in `where` clause: `_cm:u8 where checked` or `_cm where range: 0..100`
#[derive(Debug, Clone, PartialEq, Default)]
pub struct UnitReprConstraints {
    /// Explicit representation type (from compact syntax `_cm:u12`)
    pub repr: Option<ReprType>,
    /// Range constraint for auto-inferring bit width
    pub range: Option<(i64, i64)>,
    /// Overflow behavior
    pub overflow: OverflowBehavior,
    /// Default value expression
    pub default_value: Option<Box<Expr>>,
}

/// Binary arithmetic operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryArithmeticOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

/// Unary arithmetic operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryArithmeticOp {
    Neg,
    Abs,
}

/// Binary arithmetic rule: `allow add(length) -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryArithmeticRule {
    pub op: BinaryArithmeticOp,
    pub operand_type: Type,
    pub result_type: Type,
}

/// Unary arithmetic rule: `allow neg -> length`
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryArithmeticRule {
    pub op: UnaryArithmeticOp,
    pub result_type: Type,
}

/// Compound unit definition: `unit velocity = length / time`
/// Defines derived units from base unit families
#[derive(Debug, Clone, PartialEq)]
pub struct CompoundUnitDef {
    pub span: Span,
    pub name: String,         // e.g., "velocity"
    pub expr: UnitExpr,       // e.g., length / time
    pub arithmetic: Option<UnitArithmetic>,
    pub visibility: Visibility,
}

/// Unit expression for compound units
#[derive(Debug, Clone, PartialEq)]
pub enum UnitExpr {
    /// Base unit family reference
    Base(String),
    /// Multiplication: length * length
    Mul(Box<UnitExpr>, Box<UnitExpr>),
    /// Division: length / time
    Div(Box<UnitExpr>, Box<UnitExpr>),
    /// Power: time^2
    Pow(Box<UnitExpr>, i32),
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

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: trait Foo<T>
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    /// Associated types: `type Item`, `type Item: Clone`
    pub associated_types: Vec<AssociatedTypeDef>,
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,
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
pub struct ImplBlock {
    pub span: Span,
    /// Generic type parameters: impl[T]
    pub generic_params: Vec<String>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    pub target_type: Type,
    pub trait_name: Option<String>,
    /// Associated type implementations: `type Item = i64`
    pub associated_types: Vec<AssociatedTypeImpl>,
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
    /// Storage class (Auto for normal variables, Shared for GPU shared memory)
    pub storage_class: StorageClass,
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
    /// Unit type with representation constraint: `_cm:u12` or `_cm where range: 0..100`
    /// Used in bitfields and for compact storage with type safety
    UnitWithRepr {
        name: String,
        repr: Option<ReprType>,
        constraints: UnitReprConstraints,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    /// Non-blocking guarantee - cannot call blocking operations
    Async,
    /// No side effects - cannot do I/O, network, filesystem, or GC allocation
    Pure,
    /// I/O operations allowed (console, general I/O)
    Io,
    /// Network operations allowed (HTTP, TCP, UDP)
    Net,
    /// Filesystem operations allowed (read/write files, directories)
    Fs,
    /// Unsafe/unchecked operations allowed (raw pointers, FFI)
    Unsafe,
}

impl Effect {
    /// Parse an effect from a decorator name.
    /// Returns None if the name is not a recognized effect.
    pub fn from_decorator_name(name: &str) -> Option<Self> {
        match name {
            "async" => Some(Effect::Async),
            "pure" => Some(Effect::Pure),
            "io" => Some(Effect::Io),
            "net" => Some(Effect::Net),
            "fs" => Some(Effect::Fs),
            "unsafe" => Some(Effect::Unsafe),
            _ => None,
        }
    }

    /// Get the decorator name for this effect.
    pub fn decorator_name(&self) -> &'static str {
        match self {
            Effect::Async => "async",
            Effect::Pure => "pure",
            Effect::Io => "io",
            Effect::Net => "net",
            Effect::Fs => "fs",
            Effect::Unsafe => "unsafe",
        }
    }
}

/// Module capability declarations for restricting what effects are allowed.
///
/// Capabilities are declared at the module level in `__init__.spl` files
/// using the `requires [cap1, cap2]` syntax. A module can only define
/// functions with effects that are subsets of its declared capabilities.
///
/// Example:
/// ```simple
/// # In __init__.spl
/// requires [pure, io]
///
/// # This module can only contain @pure and @io functions
/// # @net or @fs functions would be compile errors
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Capability {
    /// Pure computation only - no side effects
    Pure,
    /// I/O operations (console, general I/O)
    Io,
    /// Network operations (HTTP, TCP, UDP)
    Net,
    /// Filesystem operations (read/write files, directories)
    Fs,
    /// Unsafe/unchecked operations (raw pointers, FFI)
    Unsafe,
    /// Garbage collection allowed
    Gc,
}

impl Capability {
    /// Parse a capability from its name.
    /// Returns None if the name is not a recognized capability.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "pure" => Some(Capability::Pure),
            "io" => Some(Capability::Io),
            "net" => Some(Capability::Net),
            "fs" => Some(Capability::Fs),
            "unsafe" => Some(Capability::Unsafe),
            "gc" => Some(Capability::Gc),
            _ => None,
        }
    }

    /// Get the name of this capability.
    pub fn name(&self) -> &'static str {
        match self {
            Capability::Pure => "pure",
            Capability::Io => "io",
            Capability::Net => "net",
            Capability::Fs => "fs",
            Capability::Unsafe => "unsafe",
            Capability::Gc => "gc",
        }
    }

    /// Convert an Effect to its corresponding Capability (if applicable).
    /// Note: Async is not a capability since it's about execution model, not permissions.
    pub fn from_effect(effect: &Effect) -> Option<Self> {
        match effect {
            Effect::Pure => Some(Capability::Pure),
            Effect::Io => Some(Capability::Io),
            Effect::Net => Some(Capability::Net),
            Effect::Fs => Some(Capability::Fs),
            Effect::Unsafe => Some(Capability::Unsafe),
            Effect::Async => None, // Async is execution model, not capability
        }
    }
}

/// Module capability requirements statement.
///
/// Declared in `__init__.spl` to restrict what effects functions in this
/// module (and child modules) can use.
///
/// Syntax: `requires [pure, io, net]`
///
/// Example:
/// ```simple
/// # In std_lib/src/core/__init__.spl
/// requires [pure]
///
/// # All functions in core/ must be @pure
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct RequiresCapabilitiesStmt {
    pub span: Span,
    pub capabilities: Vec<Capability>,
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
