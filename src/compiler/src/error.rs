//! Compiler error types.

use crate::value::Value;
use thiserror::Error;

/// Compilation errors.
#[derive(Error, Debug)]
pub enum CompileError {
    #[error("io: {0}")]
    Io(String),
    #[error("parse: {0}")]
    Parse(String),
    #[error("semantic: {0}")]
    Semantic(String),
    #[error("codegen: {0}")]
    Codegen(String),
    /// Error from ? operator that should be propagated as a return value
    #[error("try: early return")]
    TryError(Value),
}
