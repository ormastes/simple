use crate::token::{NumericSuffix, Span};
use super::enums::*;

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

/// Bitfield definition: `bitfield Name(base_type): fields`
/// Compact binary representation with bit-level field packing.
/// Supports unit types with explicit bit widths (e.g., `x: cm:i12`).
#[derive(Debug, Clone, PartialEq)]
pub struct BitfieldDef {
    pub span: Span,
    pub name: String,
    /// Base storage type (u8, u16, u32, u64, i8, etc.)
    pub base_type: Option<Type>,
    /// Bitfield fields with bit widths
    pub fields: Vec<BitfieldField>,
    /// Named constants (const NAME = Value)
    pub constants: Vec<BitfieldConstant>,
    pub visibility: Visibility,
    /// Attributes applied to the bitfield
    pub attributes: Vec<Attribute>,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
}

/// A single field in a bitfield
#[derive(Debug, Clone, PartialEq)]
pub struct BitfieldField {
    pub span: Span,
    pub name: String,
    /// Bit width (e.g., 1, 8, 12)
    pub bits: u8,
    /// Optional unit type with repr (e.g., cm:i12)
    pub unit_type: Option<UnitWithRepr>,
    /// Whether this is a reserved/padding field (_reserved)
    pub is_reserved: bool,
}

/// Named constant in a bitfield
#[derive(Debug, Clone, PartialEq)]
pub struct BitfieldConstant {
    pub span: Span,
    pub name: String,
    /// Constant value (literal or constructor expression)
    pub value: Expr,
}

/// Unit type with representation constraint
/// Used in bitfield fields: `cm:i12` (12-bit signed centimeters)
#[derive(Debug, Clone, PartialEq)]
pub struct UnitWithRepr {
    /// Unit suffix (e.g., "cm", "ms")
    pub unit_suffix: String,
    /// Representation type (e.g., i12, u8, f32)
    pub repr: ReprType,
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
// Unit type definitions (extracted to nodes_units.rs)
include!("nodes_units.rs");

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
    /// Attributes applied to the impl block: #[default]
    pub attributes: Vec<Attribute>,
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

/// Macro definition: macro name(params) -> (contract): body
#[derive(Debug, Clone, PartialEq)]
pub struct MacroDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<MacroParam>,
    pub contract: Vec<MacroContractItem>,
    pub body: Vec<MacroStmt>,
    pub visibility: Visibility,
}

/// A parameter in a macro definition
#[derive(Debug, Clone, PartialEq)]
pub struct MacroParam {
    pub name: String,
    pub ty: Type,
    pub is_const: bool,
}

/// Macro contract items (header-only declarations for symbol table)
#[derive(Debug, Clone, PartialEq)]
pub enum MacroContractItem {
    Returns(MacroReturns),
    Intro(MacroIntro),
    Inject(MacroInject),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroReturns {
    pub label: Option<String>,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroIntro {
    pub label: String,
    pub spec: MacroIntroSpec,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroInject {
    pub label: String,
    pub spec: MacroInjectSpec,
}

#[derive(Debug, Clone, PartialEq)]
pub enum EnclosingTarget {
    Module,
    Class,
    Struct,
    Trait,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroAnchor {
    Head,
    Tail,
    Here,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroTarget {
    Enclosing(EnclosingTarget),
    CallsiteBlock(MacroAnchor),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroIntroKind {
    Fn,
    Field,
    Type,
    Let,
    Const,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroParamSig {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroFnStub {
    pub name: String,
    pub params: Vec<MacroParamSig>,
    pub ret: Option<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroFieldStub {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroVarStub {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroTypeStub {
    pub name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroDeclStub {
    Fn(MacroFnStub),
    Field(MacroFieldStub),
    Var(MacroVarStub),
    Type(MacroTypeStub),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroIntroDecl {
    pub target: MacroTarget,
    pub kind: MacroIntroKind,
    pub stub: MacroDeclStub,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroConstRange {
    pub start: Expr,
    pub end: Expr,
    pub inclusive: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroIntroSpec {
    Decl(MacroIntroDecl),
    For {
        name: String,
        range: MacroConstRange,
        body: Vec<MacroIntroSpec>,
    },
    If {
        condition: Expr,
        then_body: Vec<MacroIntroSpec>,
        else_body: Vec<MacroIntroSpec>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum MacroCodeKind {
    Stmt,
    Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroInjectSpec {
    pub anchor: MacroAnchor,
    pub code_kind: MacroCodeKind,
}

/// Macro body statements
#[derive(Debug, Clone, PartialEq)]
pub enum MacroStmt {
    ConstEval(Block),
    Emit { label: String, block: Block },
    Stmt(Node),
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
    /// Reference capability wrapper (mut T, iso T)
    /// Tracks what operations are permitted on a reference
    Capability {
        capability: super::enums::ReferenceCapability,
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

// ============================================================================
// Gherkin-Style System Test DSL (doc/spec/gherkin_dsl.md)
// ============================================================================
// NOTE: Gherkin syntax is now transformed to regular Simple AST during parsing:
// - feature("name", do_block) - function call with DoBlock body
// - scenario("name", do_block) - function call with DoBlock body
// - given/when/then/and_then("pattern", do_block) - function calls
// - examples("name", [...]) - function call with array literal
//
// No special AST node types needed - uses existing Expr::Call and Expr::DoBlock.
// See src/parser/src/statements/gherkin.rs for the transformation logic.

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
