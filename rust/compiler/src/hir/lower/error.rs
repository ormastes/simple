use simple_parser::Span;
use thiserror::Error;

use super::super::lifetime::LifetimeViolation;
use super::super::types::TypeId;
use super::memory_warning::{MemoryWarningCode, MemoryWarningCollector};

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("Unknown type: {type_name}")]
    UnknownType {
        type_name: String,
        /// Available type names for suggestions
        available_types: Vec<String>,
    },

    #[error("Unknown variable: {0}")]
    UnknownVariable(String),

    /// E1032: self used in static method
    #[error("cannot use `self` in static method")]
    SelfInStatic,

    /// E1016: let binding failed - complex pattern not supported
    #[error("let binding failed: {pattern} - complex patterns are not yet supported in let bindings")]
    LetBindingFailed { pattern: String },

    #[error("Type mismatch: expected {expected:?}, found {found:?}")]
    TypeMismatch { expected: TypeId, found: TypeId },

    #[error("Cannot infer type")]
    CannotInferType,

    #[error("Cannot infer type: {0}")]
    CannotInferTypeFor(String),

    #[error("Parameter '{0}' requires explicit type annotation")]
    MissingParameterType(String),

    #[error("Cannot infer element type of empty array - use explicit annotation")]
    EmptyArrayNeedsType,

    #[error("Cannot infer field type: struct '{struct_name}' field '{field}'")]
    CannotInferFieldType {
        struct_name: String,
        field: String,
        /// Available field names for suggestions
        available_fields: Vec<String>,
    },

    #[error("Cannot infer element type for index into '{0}'")]
    CannotInferIndexType(String),

    #[error("Cannot infer deref type for '{0}'")]
    CannotInferDerefType(String),

    #[error("Unsupported feature: {0}")]
    Unsupported(String),

    /// E1050: Use Python-style constructor instead of .new()
    #[error("Use Python-style constructor `{class_name}(...)` instead of `{class_name}.new(...)`")]
    UseConstructorNotNew { class_name: String },

    /// E1051: Static method not supported in native compilation
    #[error("Static method `{class_name}.{method_name}()` not yet supported in native compilation. Use interpreter mode or define as a free function")]
    StaticMethodNotSupported { class_name: String, method_name: String },

    /// E1052: Attempted to mutate self in an immutable fn method
    #[error("cannot modify self in immutable fn method. Use `me` instead of `fn` to allow self mutation")]
    SelfMutationInImmutableMethod,

    /// CTR-032: Impure function call in contract expression
    #[error(
        "Impure function call '{func_name}' in contract expression. Only #[pure] functions can be called in contracts"
    )]
    ImpureFunctionInContract { func_name: String },

    /// CTR-060-062: Non-snapshot-safe type in old() expression
    #[error(
        "Type is not snapshot-safe for old() expression. Only primitives, enums, and immutable structs can be captured"
    )]
    NotSnapshotSafe,

    /// Capability error (aliasing, conversion, mode compatibility)
    #[error("Capability error: {0}")]
    Capability(#[from] super::super::capability::CapabilityError),

    /// Module resolution error (cannot find or load imported module)
    #[error("Module resolution error: {0}")]
    ModuleResolution(String),

    /// Lifetime violation errors (E2001-E2006)
    #[error("{}", .0.description())]
    LifetimeViolation(LifetimeViolation),

    /// Multiple lifetime violations
    #[error("Multiple lifetime violations detected ({} errors)", .0.len())]
    LifetimeViolations(Vec<LifetimeViolation>),

    /// Memory safety violation (strict mode - Rust-level safety)
    /// W1001-W1006 become compile errors in strict mode
    #[error("Memory safety error [{code}]: {message}")]
    MemorySafetyViolation {
        /// The warning code that became an error
        code: MemoryWarningCode,
        /// Human-readable error message
        message: String,
        /// Source location
        span: Span,
        /// All collected warnings (for detailed diagnostics)
        all_warnings: MemoryWarningCollector,
    },
}

pub type LowerResult<T> = Result<T, LowerError>;
