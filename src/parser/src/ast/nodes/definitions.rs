//! Definition AST nodes (functions, structs, classes, traits, etc.)

use crate::token::Span;
use super::super::enums::*;
use super::core::*;
use super::contracts::*;

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

/// Standalone unit type definition
/// Single-base: `unit UserId: i64 as uid`
/// Multi-base:  `unit IpAddr: str | u32 as ip` (accepts string or numeric literals)
/// Creates a newtype wrapper with literal suffix support
// Unit type definitions (extracted to nodes_units.rs)
include!("../nodes_units.rs");

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
