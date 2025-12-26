//! Linker error types.

use std::path::PathBuf;
use thiserror::Error;

/// Linker error types.
#[derive(Error, Debug)]
pub enum LinkerError {
    /// No suitable linker found on the system.
    #[error("no suitable linker found (tried mold, lld, ld)")]
    NoLinkerFound,

    /// Specified linker not found.
    #[error("linker '{0}' not found")]
    LinkerNotFound(String),

    /// Linker execution failed.
    #[error("linker failed with exit code {exit_code}: {message}")]
    LinkerFailed {
        exit_code: i32,
        message: String,
        stderr: String,
    },

    /// Linker was killed by signal.
    #[error("linker killed by signal")]
    LinkerKilled,

    /// IO error during linking.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// Missing object file.
    #[error("object file not found: {0}")]
    ObjectNotFound(PathBuf),

    /// Invalid linker configuration.
    #[error("invalid linker configuration: {0}")]
    InvalidConfig(String),

    /// Unsupported platform for native linking.
    #[error("native linking not supported on this platform")]
    UnsupportedPlatform,

    /// Symbol resolution error.
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),

    /// Multiple definition error.
    #[error("multiple definition of symbol: {0}")]
    MultipleDefinition(String),
}

/// Result type for linker operations.
pub type LinkerResult<T> = Result<T, LinkerError>;
