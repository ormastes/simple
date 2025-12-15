use thiserror::Error;

use super::super::types::TypeId;

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("Unknown type: {0}")]
    UnknownType(String),

    #[error("Unknown variable: {0}")]
    UnknownVariable(String),

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
    CannotInferFieldType { struct_name: String, field: String },

    #[error("Cannot infer element type for index into '{0}'")]
    CannotInferIndexType(String),

    #[error("Cannot infer deref type for '{0}'")]
    CannotInferDerefType(String),

    #[error("Unsupported feature: {0}")]
    Unsupported(String),
}

pub type LowerResult<T> = Result<T, LowerError>;
