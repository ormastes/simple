//! Definition AST nodes (functions, structs, classes, traits, etc.)

use std::collections::HashMap;

use super::super::enums::*;
use super::contracts::*;
use super::core::*;
use crate::token::Span;

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
    /// Whether this function is explicitly marked as sync (non-suspending)
    /// sync fn = cannot contain suspension operators (~=, if~, while~, for~)
    /// Default (false) = async-by-default, may suspend
    pub is_sync: bool,
    /// Bounds block for @simd kernels (trailing bounds: clause)
    pub bounds_block: Option<BoundsBlock>,
    /// Whether this is a static method (no self parameter, can be called on type)
    /// static fn = ClassName.method() syntax allowed
    /// Default (false) = instance method, requires self
    pub is_static: bool,
    /// Whether this is a mutable method (uses `me` keyword instead of `fn`)
    /// Mutable methods can modify self and the changes persist
    pub is_me_method: bool,
    /// Whether this is a generator function (uses `gen` keyword)
    /// Generator functions collect yield values and return a Generator
    pub is_generator: bool,
    /// Return type constraint for dependent function types (VER-011)
    /// Syntax: `fn f(x: T) -> U where result.len() == x.len():`
    /// The predicate can reference `result` and function parameters
    pub return_constraint: Option<Expr>,

    // Generic template metadata for .smf template storage
    /// True if this is an unspecialized generic template
    pub is_generic_template: bool,
    /// Base template name if this is a specialization
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Int)
    pub type_bindings: HashMap<String, Type>,
}

impl FunctionDef {
    /// Check if this function is marked as pure via @pure effect or #[pure] attribute.
    /// Pure functions cannot perform I/O, network, filesystem, or GC operations.
    /// Pure functions can be called from contract expressions (CTR-031).
    pub fn is_pure(&self) -> bool {
        self.effects.contains(&Effect::Pure) || self.attributes.iter().any(|attr| attr.name == "pure")
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
        self.decorators
            .iter()
            .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "simd"))
    }

    /// Check if this function has the @property_test decorator.
    /// Property tests generate random inputs to verify invariant properties.
    pub fn is_property_test(&self) -> bool {
        self.decorators
            .iter()
            .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "property_test"))
    }

    /// Check if this function has the @snapshot_test decorator.
    /// Snapshot tests capture and compare output against stored golden files.
    pub fn is_snapshot_test(&self) -> bool {
        self.decorators
            .iter()
            .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "snapshot_test"))
    }

    /// Check if this function is any kind of test (unit, property, or snapshot).
    /// Includes functions with @test, @property_test, or @snapshot_test decorators.
    pub fn is_test(&self) -> bool {
        self.decorators.iter().any(|d| {
            matches!(&d.name, Expr::Identifier(name)
                if name == "test" || name == "property_test" || name == "snapshot_test")
        })
    }

    /// Get property test configuration parameters from @property_test(iterations: N, ...).
    /// Returns None if not a property test or no parameters specified.
    pub fn property_test_config(&self) -> Option<&Vec<Argument>> {
        self.decorators
            .iter()
            .find(|d| matches!(&d.name, Expr::Identifier(name) if name == "property_test"))
            .and_then(|d| d.args.as_ref())
    }

    /// Get snapshot test configuration parameters from @snapshot_test(name: "...", format: "...").
    /// Returns None if not a snapshot test or no parameters specified.
    pub fn snapshot_test_config(&self) -> Option<&Vec<Argument>> {
        self.decorators
            .iter()
            .find(|d| matches!(&d.name, Expr::Identifier(name) if name == "snapshot_test"))
            .and_then(|d| d.args.as_ref())
    }

    /// Check if this function was generated by an LLM or code generation tool.
    /// Functions with @generated_by decorator include provenance metadata for auditing.
    pub fn is_generated(&self) -> bool {
        self.decorators
            .iter()
            .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "generated_by"))
    }

    /// Get provenance metadata from @generated_by(tool: "...", version: "...", ...).
    /// Returns None if not a generated function or no metadata specified.
    /// Metadata includes: tool, version, prompt_hash, timestamp, session_id, verified, reviewer, review_date.
    pub fn generated_by_metadata(&self) -> Option<&Vec<Argument>> {
        self.decorators
            .iter()
            .find(|d| matches!(&d.name, Expr::Identifier(name) if name == "generated_by"))
            .and_then(|d| d.args.as_ref())
    }

    /// Check if this function is marked as ghost via @ghost effect.
    /// Ghost functions exist only for verification and are erased at runtime.
    /// They are included in Lean output but not in compiled code.
    pub fn is_ghost(&self) -> bool {
        self.effects.contains(&Effect::Ghost)
    }

    /// Check if this function is marked for verification via @verify effect.
    /// Verified functions follow the verified subset (no unsafe, no reflection)
    /// and generate Lean proofs.
    pub fn is_verify(&self) -> bool {
        self.effects.contains(&Effect::Verify)
    }

    /// Check if this function is a trusted boundary via @trusted effect.
    /// Trusted functions mark the interface between verified and unverified code.
    pub fn is_trusted(&self) -> bool {
        self.effects.contains(&Effect::Trusted)
    }

    /// Check if this function has any verification-related effects.
    /// Returns true if function is ghost, verify, or trusted.
    pub fn is_verification_related(&self) -> bool {
        self.effects.iter().any(|e| e.is_verification())
    }

    /// Check if this function has a termination measure (decreases clause).
    /// Termination measures are used for Lean verification but not checked at runtime.
    pub fn has_decreases(&self) -> bool {
        self.contract.as_ref().map_or(false, |c| c.has_decreases())
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

    // Generic template metadata for .smf template storage
    /// True if this is an unspecialized generic template
    pub is_generic_template: bool,
    /// Base template name if this is a specialization
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Int)
    pub type_bindings: HashMap<String, Type>,
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
    /// Effect annotations: @ghost, @verify (similar to function effects)
    /// Used primarily for verification-related effects on class definitions
    pub effects: Vec<Effect>,
    /// Attributes applied to the class: #[deprecated]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,

    // Generic template metadata for .smf template storage
    /// True if this is an unspecialized generic template
    pub is_generic_template: bool,
    /// Base template name if this is a specialization
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Int)
    pub type_bindings: HashMap<String, Type>,
    /// Class invariant (checked after constructor and public methods)
    pub invariant: Option<InvariantBlock>,
    /// Macro invocations in class body (expanded at runtime to add fields/methods)
    pub macro_invocations: Vec<MacroInvocation>,
    /// Mixin applications: use MixinName
    pub mixins: Vec<MixinRef>,
}

impl ClassDef {
    /// Check if this class is marked with #[snapshot] attribute (CTR-062)
    /// Types with #[snapshot] have custom snapshot semantics for old() expressions.
    pub fn is_snapshot(&self) -> bool {
        self.attributes.iter().any(|attr| attr.name == "snapshot")
    }

    /// Check if this class is marked as ghost via @ghost effect.
    /// Ghost classes exist only for verification and are erased at runtime.
    /// They are included in Lean output but not in compiled code.
    pub fn is_ghost(&self) -> bool {
        self.effects.contains(&Effect::Ghost)
    }

    /// Check if this class is marked for verification via @verify effect.
    /// Verified classes follow the verified subset and generate Lean proofs.
    pub fn is_verify(&self) -> bool {
        self.effects.contains(&Effect::Verify)
    }

    /// Check if this class has any verification-related effects.
    /// Returns true if class is ghost or verify.
    pub fn is_verification_related(&self) -> bool {
        self.effects.iter().any(|e| e.is_verification())
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
    /// Methods defined inside the enum block
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
    /// Attributes like #[strong]
    pub attributes: Vec<Attribute>,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,

    // Generic template metadata for .smf template storage
    /// True if this is an unspecialized generic template
    pub is_generic_template: bool,
    /// Base template name if this is a specialization
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Int)
    pub type_bindings: HashMap<String, Type>,
}

// Standalone unit type definition
// Single-base: `unit UserId: i64 as uid`
// Multi-base:  `unit IpAddr: str | u32 as ip` (accepts string or numeric literals)
// Creates a newtype wrapper with literal suffix support
// Unit type definitions (extracted to nodes_units.rs)
include!("../nodes_units.rs");

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
    pub span: Span,
    pub name: String,
    /// Generic type parameters: trait Foo<T>
    pub generic_params: Vec<String>,
    /// Super traits (trait inheritance): trait Copy: Clone, trait Seq<T>: Collection<T>
    /// Contains trait types that this trait extends (supports generics)
    pub super_traits: Vec<Type>,
    /// Where clause for trait bounds: where T: Clone + Default
    pub where_clause: WhereClause,
    /// Associated types: `type Item`, `type Item: Clone`
    pub associated_types: Vec<AssociatedTypeDef>,
    pub methods: Vec<FunctionDef>,
    pub visibility: Visibility,
    /// Documentation comment for API doc generation
    pub doc_comment: Option<DocComment>,

    // Generic template metadata for .smf template storage
    /// True if this is an unspecialized generic template
    pub is_generic_template: bool,
    /// Base template name if this is a specialization
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Type)
    pub type_bindings: HashMap<String, Type>,
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

/// Interface binding for static polymorphism
/// Syntax: `bind Interface = ImplType`
///
/// Binds an interface (trait) to a specific implementation type at package scope,
/// enabling static dispatch (monomorphization) while preserving type safety.
///
/// Example:
/// ```simple
/// # In __init__.spl
/// bind Logger = ConsoleLogger
/// bind Serializer = JsonSerializer
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceBinding {
    pub span: Span,
    /// The interface/trait name being bound
    pub interface_name: String,
    /// The implementation type to bind to
    pub impl_type: Type,
    /// Optional documentation
    pub doc_comment: Option<DocComment>,
}

/// Mixin definition: mixin Name[T] requires Trait: fields and methods
/// Mixins provide reusable field and method compositions for classes and structs.
/// Feature #2200: Mixin Declaration Syntax
#[derive(Debug, Clone, PartialEq)]
pub struct MixinDef {
    pub span: Span,
    pub name: String,
    pub generic_params: Vec<String>,
    pub required_traits: Vec<String>,
    pub required_mixins: Vec<String>,
    pub fields: Vec<Field>,
    pub methods: Vec<FunctionDef>,
    pub required_methods: Vec<RequiredMethodSig>,
    pub visibility: Visibility,
    pub doc_comment: Option<DocComment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RequiredMethodSig {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MixinRef {
    pub span: Span,
    pub name: String,
    pub type_args: Vec<Type>,
    pub overrides: Vec<OverrideSpec>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OverrideSpec {
    Override(String),
    Hide(String),
    Rename { old_name: String, new_name: String },
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

/// Class/struct/enum alias definition
///
/// Syntax: `alias NewName = OldName`
///
/// Creates an alias for an existing class, struct, or enum type.
/// Useful for renaming types or creating shorter names.
///
/// # Example
/// ```simple
/// alias Point2D = Point
/// alias Optional = Option   # Generic type alias
///
/// @deprecated("Use Point2D instead")
/// alias OldPoint = Point
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ClassAliasDef {
    pub span: Span,
    /// The new alias name
    pub name: String,
    /// The original type name being aliased
    pub target: String,
    pub visibility: Visibility,
    /// Decorators applied to the alias: @deprecated("Use X instead")
    pub decorators: Vec<Decorator>,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
}

/// Function alias definition
///
/// Syntax: `fn new_name = old_name` (top-level)
/// Syntax: `fn new_name = old_name` (in impl block)
///
/// Creates an alias for an existing function.
/// The alias can be deprecated to guide users to a new name.
///
/// # Example
/// ```simple
/// fn println = print        # Top-level alias
///
/// @deprecated("Use println instead")
/// fn old_print = print
///
/// impl List:
///     fn each = iter        # Method alias
///     fn forEach = each     # Chain aliases
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionAliasDef {
    pub span: Span,
    /// The new alias name
    pub name: String,
    /// The original function name being aliased
    pub target: String,
    pub visibility: Visibility,
    /// Decorators applied to the alias: @deprecated("Use X instead")
    pub decorators: Vec<Decorator>,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExternDef {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
    pub visibility: Visibility,
    pub attributes: Vec<Attribute>,
}

/// External class definition for FFI object-based bindings.
///
/// Syntax:
/// ```simple
/// extern class Database:
///     static fn open(url: text) -> Result<Database, DbError>
///     fn query(sql: text) -> Result<Rows, DbError>
///     me execute(sql: text) -> Result<Int, DbError>
///     fn close()
/// ```
///
/// External classes wrap Rust objects through the FFI system.
/// - `static fn` - static factory methods (no self parameter)
/// - `fn` - immutable methods (takes &self)
/// - `me` - mutable methods (takes &mut self)
#[derive(Debug, Clone, PartialEq)]
pub struct ExternClassDef {
    pub span: Span,
    /// Class name (e.g., "Database")
    pub name: String,
    /// Generic type parameters (e.g., `<T, U>`)
    pub generic_params: Vec<String>,
    /// Methods exposed by this external class
    pub methods: Vec<ExternMethodDef>,
    /// Visibility (pub/private)
    pub visibility: Visibility,
    /// Attributes (e.g., `#[ffi_type = "Database"]`)
    pub attributes: Vec<Attribute>,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
}

/// Method kind for extern class methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternMethodKind {
    /// Static method (no self parameter): `static fn open(...)`
    Static,
    /// Immutable method (takes &self): `fn query(...)`
    Immutable,
    /// Mutable method (takes &mut self): `me execute(...)`
    Mutable,
}

/// Method definition for extern class.
#[derive(Debug, Clone, PartialEq)]
pub struct ExternMethodDef {
    pub span: Span,
    /// Method name
    pub name: String,
    /// Method kind (static/immutable/mutable)
    pub kind: ExternMethodKind,
    /// Parameters (excluding self)
    pub params: Vec<Parameter>,
    /// Return type (None for void methods)
    pub return_type: Option<Type>,
    /// Attributes on this method
    pub attributes: Vec<Attribute>,
    /// Documentation comment
    pub doc_comment: Option<DocComment>,
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
    /// Whether this is a variadic parameter (...name)
    pub is_variadic: bool,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// Literal function definition for custom string suffix handling.
///
/// Syntax: `literal fn _suffix(param: text) -> ReturnType: body`
///
/// Literal functions provide explicit control over suffix → type mapping.
/// When a string literal like "value"_suffix is encountered:
/// 1. Check LITERAL_FUNCTIONS registry for explicit override
/// 2. If found, call the literal function with the string value
/// 3. If not found, fall back to suffix → type name conversion
///
/// # Example
/// ```simple
/// literal fn _re(s: text) -> Regex:
///     Regex.compile(s)
///
/// val pattern = "test"_re  # Calls the literal fn, returns Regex
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralFunctionDef {
    pub span: Span,
    /// The suffix without leading underscore (e.g., "re" for _re)
    pub suffix: String,
    /// The parameter name for the string value
    pub param_name: String,
    /// The return type
    pub return_type: Option<Type>,
    /// The function body
    pub body: Block,
    /// Optional documentation comment
    pub doc_comment: Option<DocComment>,
}
