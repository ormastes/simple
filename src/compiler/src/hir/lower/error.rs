use thiserror::Error;

use super::super::types::TypeId;

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
}

pub type LowerResult<T> = Result<T, LowerError>;
