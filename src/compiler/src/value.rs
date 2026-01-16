//! Value types for the interpreter.
//!
//! This module contains the runtime value representation and
//! pointer wrapper types for manual memory management.

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};

use simple_common::actor::ActorHandle;
use simple_common::manual_mem::{
    Handle as ManualHandle, HandlePool as ManualHandlePool, ManualGc, Shared as ManualShared, Unique as ManualUnique,
    WeakPtr as ManualWeak,
};
use simple_parser::ast::{Expr, FunctionDef, Node};

use crate::error::CompileError;

// Async value types (Future, Generator, Channel, ThreadPool)
// These are split into a separate file for maintainability
include!("value_async.rs");

// Mock and Spy types for testing
include!("value_mock.rs");

//==============================================================================
// Magic Names (for formal verification)
//==============================================================================
// These constants define the special names used by the interpreter.
// Making them constants ensures consistency and enables Lean verification.
//
// Lean equivalent:
//   def BUILTIN_RANGE : String := "__range__"
//   def BUILTIN_ARRAY : String := "__array__"
//   def METHOD_NEW : String := "new"
//   def METHOD_SELF : String := "self"
//   def METHOD_MISSING : String := "method_missing"
//   def FUNC_MAIN : String := "main"
//   def ATTR_STRONG : String := "strong"

/// Magic class name for range objects created by range() or `..` syntax
pub const BUILTIN_RANGE: &str = "__range__";

/// Magic class name for array-like objects
pub const BUILTIN_ARRAY: &str = "__array__";

//==============================================================================
// Special Method Names (for formal verification)
//==============================================================================

/// Constructor method name
pub const METHOD_NEW: &str = "new";

/// Self parameter name
pub const METHOD_SELF: &str = "self";

/// Method missing hook name (Ruby-style metaprogramming)
pub const METHOD_MISSING: &str = "method_missing";

/// Entry point function name
pub const FUNC_MAIN: &str = "main";

//==============================================================================
// Special Attribute Names (for formal verification)
//==============================================================================

/// Strong enum attribute (enforces exhaustive matching)
pub const ATTR_STRONG: &str = "strong";

//==============================================================================
// Built-in Type/Function Names (for formal verification)
//==============================================================================

/// Channel constructor name
pub const BUILTIN_CHANNEL: &str = "Channel";

/// Spawn function name for actor creation
pub const BUILTIN_SPAWN: &str = "spawn";

/// Join function name for actor synchronization
pub const BUILTIN_JOIN: &str = "join";

/// Reply function name for actor message response
pub const BUILTIN_REPLY: &str = "reply";

/// User-facing Range class name (alias for BUILTIN_RANGE)
pub const CLASS_RANGE: &str = "Range";

/// User-facing Array class name (alias for BUILTIN_ARRAY)
pub const CLASS_ARRAY: &str = "Array";

//==============================================================================
// Builtin Operation Categories (for formal verification)
//==============================================================================
// These arrays define categories of builtin operations for effect analysis.
// Making them constants enables Lean verification of effect properties.

/// Blocking operations - cannot be used in async contexts
pub const BLOCKING_BUILTINS: &[&str] = &[
    "await",
    "join",
    "recv",
    "sleep",
    "input",
    "read_file",
    "write_file",
    // Native filesystem operations
    "native_fs_read",
    "native_fs_write",
    "native_fs_append",
    "native_fs_create_dir",
    "native_fs_remove_file",
    "native_fs_remove_dir",
    "native_fs_rename",
    "native_fs_copy",
    "native_fs_metadata",
    "native_fs_read_dir",
    "native_fs_open",
    "native_file_read",
    "native_file_write",
    "native_file_flush",
    "native_file_seek",
    "native_file_sync",
    "native_file_close",
    // Native terminal operations
    "native_term_read",
    "native_term_write",
    "native_term_read_timeout",
    "native_term_flush",
    "native_term_poll",
];

/// Actor operations - require actor runtime
pub const ACTOR_BUILTINS: &[&str] = &["spawn", "send", "recv", "reply", "join"];

/// Generator operations - require generator runtime
pub const GENERATOR_BUILTINS: &[&str] = &["generator", "next", "collect"];

/// Built-in class types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive BuiltinClass
///   | range   -- Range objects (start..end)
///   | array   -- Array-like objects
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinClass {
    /// Range type: represents a range of values
    Range,
    /// Array type: built-in array wrapper
    Array,
}

impl BuiltinClass {
    /// Try to parse a class name as a built-in class.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "__range__" | "Range" => Some(BuiltinClass::Range),
            "__array__" | "Array" => Some(BuiltinClass::Array),
            _ => None,
        }
    }

    /// Get the internal string name of this built-in class.
    pub fn as_str(&self) -> &'static str {
        match self {
            BuiltinClass::Range => BUILTIN_RANGE,
            BuiltinClass::Array => BUILTIN_ARRAY,
        }
    }

    /// Check if the given class name matches this built-in class.
    pub fn matches(&self, name: &str) -> bool {
        match self {
            BuiltinClass::Range => name == BUILTIN_RANGE || name == CLASS_RANGE,
            BuiltinClass::Array => name == BUILTIN_ARRAY || name == CLASS_ARRAY,
        }
    }
}

/// Classification of a class type - either builtin or user-defined.
///
/// Lean equivalent:
/// ```lean
/// inductive ClassType
///   | builtin (b : BuiltinClass)
///   | user (name : String)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassType {
    /// A built-in class with special handling
    Builtin(BuiltinClass),
    /// A user-defined class
    User(String),
}

impl ClassType {
    /// Classify a class name as either builtin or user-defined.
    pub fn from_name(name: &str) -> Self {
        match BuiltinClass::from_name(name) {
            Some(builtin) => ClassType::Builtin(builtin),
            None => ClassType::User(name.to_string()),
        }
    }

    /// Check if this is a built-in class.
    pub fn is_builtin(&self) -> bool {
        matches!(self, ClassType::Builtin(_))
    }

    /// Check if this is the range type.
    pub fn is_range(&self) -> bool {
        matches!(self, ClassType::Builtin(BuiltinClass::Range))
    }
}

//==============================================================================
// Method Lookup (for formal verification)
//==============================================================================
// These types replace magic string "method_missing" with explicit enum variants.
// This makes method dispatch logic verifiable.
// Note: METHOD_MISSING constant is defined above with other special names.

/// Result of looking up a method on a type.
///
/// Lean equivalent:
/// ```lean
/// inductive MethodLookupResult
///   | found           -- Regular method found
///   | notFound        -- Method not found, no fallback
///   | missingHook     -- method_missing fallback available
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodLookupResult {
    /// Regular method was found
    Found,
    /// Method not found and no method_missing hook
    NotFound,
    /// Method not found but method_missing hook is available
    MissingHook,
}

impl MethodLookupResult {
    /// Check if a method was found (either direct or via method_missing).
    pub fn is_callable(&self) -> bool {
        matches!(self, MethodLookupResult::Found | MethodLookupResult::MissingHook)
    }

    /// Check if this is the method_missing fallback.
    pub fn is_missing_hook(&self) -> bool {
        matches!(self, MethodLookupResult::MissingHook)
    }
}

/// Variable environment for compile-time evaluation
pub type Env = HashMap<String, Value>;

thread_local! {
    pub(crate) static MANUAL_GC: ManualGc = ManualGc::new();
}

/// NewType for class/struct names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure ClassName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassName(pub String);

impl ClassName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for ClassName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for ClassName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum type names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure EnumTypeName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumTypeName(pub String);

impl EnumTypeName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for EnumTypeName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for EnumTypeName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

/// NewType for enum variant names - improves type safety for formal verification.
/// In Lean 4, this becomes: `structure VariantName where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantName(pub String);

impl VariantName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for VariantName {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

impl From<String> for VariantName {
    fn from(s: String) -> Self {
        Self(s)
    }
}

//==============================================================================
// Special Enum Types (for formal verification)
//==============================================================================
// These enums replace magic string comparisons for built-in enum types.
// This enables more precise verification and eliminates string-based dispatch.

/// Built-in enum types with special handling.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumType
///   | option  -- Option<T> (Some/None)
///   | result  -- Result<T, E> (Ok/Err)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumType {
    /// Option type: Some(T) | None
    Option,
    /// Result type: Ok(T) | Err(E)
    Result,
}

impl SpecialEnumType {
    /// Try to parse an enum name as a special enum type.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Option" => Some(SpecialEnumType::Option),
            "Result" => Some(SpecialEnumType::Result),
            _ => None,
        }
    }

    /// Get the string name of this special enum type.
    pub fn as_str(&self) -> &'static str {
        match self {
            SpecialEnumType::Option => "Option",
            SpecialEnumType::Result => "Result",
        }
    }
}

/// Option enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive OptionVariant
///   | some
///   | none
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptionVariant {
    Some,
    None,
}

impl OptionVariant {
    /// Try to parse a variant name as an Option variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Some" => Some(OptionVariant::Some),
            "None" => Some(OptionVariant::None),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            OptionVariant::Some => "Some",
            OptionVariant::None => "None",
        }
    }
}

/// Result enum variants.
///
/// Lean equivalent:
/// ```lean
/// inductive ResultVariant
///   | ok
///   | err
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultVariant {
    Ok,
    Err,
}

impl ResultVariant {
    /// Try to parse a variant name as a Result variant.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "Ok" => Some(ResultVariant::Ok),
            "Err" => Some(ResultVariant::Err),
            _ => None,
        }
    }

    /// Get the string name of this variant.
    pub fn as_str(&self) -> &'static str {
        match self {
            ResultVariant::Ok => "Ok",
            ResultVariant::Err => "Err",
        }
    }
}

/// Represents the kind of special enum value, combining type and variant.
///
/// Lean equivalent:
/// ```lean
/// inductive SpecialEnumValue
///   | optionSome (payload : Value)
///   | optionNone
///   | resultOk (payload : Value)
///   | resultErr (payload : Value)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialEnumKind {
    /// Option::Some
    OptionSome,
    /// Option::None
    OptionNone,
    /// Result::Ok
    ResultOk,
    /// Result::Err
    ResultErr,
}

impl SpecialEnumKind {
    /// Try to parse enum_name and variant as a special enum kind.
    pub fn from_names(enum_name: &str, variant: &str) -> Option<Self> {
        match (enum_name, variant) {
            ("Option", "Some") => Some(SpecialEnumKind::OptionSome),
            ("Option", "None") => Some(SpecialEnumKind::OptionNone),
            ("Result", "Ok") => Some(SpecialEnumKind::ResultOk),
            ("Result", "Err") => Some(SpecialEnumKind::ResultErr),
            _ => None,
        }
    }

    /// Check if this is an Option variant.
    pub fn is_option(&self) -> bool {
        matches!(self, SpecialEnumKind::OptionSome | SpecialEnumKind::OptionNone)
    }

    /// Check if this is a Result variant.
    pub fn is_result(&self) -> bool {
        matches!(self, SpecialEnumKind::ResultOk | SpecialEnumKind::ResultErr)
    }
}

/// Runtime value representation.
#[derive(Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Symbol(String),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Dict(HashMap<String, Value>),
    Lambda {
        params: Vec<String>,
        body: Box<Expr>,
        env: Env,
    },
    /// A block closure - used for BDD DSL colon-blocks like `describe "name": body`
    /// Contains a list of statements to execute when called
    BlockClosure {
        nodes: Vec<Node>,
        env: Env,
    },
    /// A function reference - used for decorators and first-class functions
    /// Includes captured environment for closure semantics
    Function {
        name: String,
        def: Box<FunctionDef>,
        captured_env: Env,
    },
    Object {
        class: String,
        fields: HashMap<String, Value>,
    },
    Enum {
        enum_name: String,
        variant: String,
        payload: Option<Box<Value>>,
    },
    /// Union type value - wraps a value with its type index
    /// Represents values of union types like `str | i64`
    Union {
        /// Index of the actual type in the union's variant list
        type_index: usize,
        /// The actual value
        inner: Box<Value>,
    },
    /// Constructor reference - a class that can be used to create instances
    /// Used for constructor polymorphism: Constructor[T] type
    Constructor {
        class_name: String,
    },
    /// Enum type reference - allows EnumName.VariantName syntax
    /// Used for enum variant construction: Color.Red, Option.Some(x)
    EnumType {
        enum_name: String,
    },
    /// Enum variant constructor - callable to create enum with payload
    /// Used for variants with data: Option.Some(x), Result.Ok(value)
    EnumVariantConstructor {
        enum_name: String,
        variant_name: String,
    },
    /// Dynamic trait object - wraps a value with its trait for dynamic dispatch
    /// Enables polymorphism via trait implementations (dyn Trait syntax)
    TraitObject {
        trait_name: String,
        inner: Box<Value>,
    },
    /// Unit value - wraps a numeric value with its unit suffix
    /// Enables type-safe unit arithmetic and conversion methods
    Unit {
        value: Box<Value>,
        suffix: String,
        family: Option<String>, // Name of unit family for conversions
    },
    Actor(ActorHandle),
    Future(FutureValue),
    Generator(GeneratorValue),
    Channel(ChannelValue),
    ThreadPool(ThreadPoolValue),
    Unique(ManualUniqueValue),
    Shared(ManualSharedValue),
    Weak(ManualWeakValue),
    Handle(ManualHandleValue),
    Borrow(BorrowValue),
    BorrowMut(BorrowMutValue),
    /// Mock object for testing - stores method configurations and call records
    Mock(MockValue),
    /// Argument matcher for mock verification
    Matcher(MatcherValue),
    /// Native callable for interpreter intrinsics (internal use only).
    NativeFunction(NativeFunction),
    /// Custom block value - result of evaluating m{}, sh{}, sql{}, re{}, etc.
    /// Stores the block kind and payload for block-specific processing.
    Block {
        kind: String,               // Block kind: "m", "sh", "sql", "re", "md", "html", "graph", "img"
        payload: String,            // Raw payload content
        result: Option<Box<Value>>, // Parsed/evaluated result (lazily computed)
    },
    Nil,
}

pub struct NativeFunction {
    pub name: String,
    pub func: Arc<dyn Fn(&[Value]) -> Result<Value, CompileError> + Send + Sync>,
}

impl fmt::Debug for NativeFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeFunction({})", self.name)
    }
}

impl Clone for NativeFunction {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            func: Arc::clone(&self.func),
        }
    }
}

// Value implementation methods
include!("value_impl.rs");

// Pointer wrappers (Manual memory management, Borrow types)
include!("value_pointers.rs");

// Include tests from separate file
include!("value_tests.rs");
