//! Error types for WASM runtime

use thiserror::Error;

/// Result type for WASM operations
pub type WasmResult<T> = Result<T, WasmError>;

/// Errors that can occur during WASM execution
#[derive(Error, Debug)]
pub enum WasmError {
    /// WASM feature not enabled
    #[error("WASM feature not enabled. Build with --features wasm")]
    FeatureNotEnabled,

    /// Module compilation failed
    #[error("Failed to compile WASM module: {0}")]
    CompilationFailed(String),

    /// Module instantiation failed
    #[error("Failed to instantiate WASM module: {0}")]
    InstantiationFailed(String),

    /// Function not found in module
    #[error("Function '{0}' not found in WASM module")]
    FunctionNotFound(String),

    /// Function call failed
    #[error("WASM function call failed: {0}")]
    CallFailed(String),

    /// Type conversion error
    #[error("Failed to convert between RuntimeValue and WasmValue: {0}")]
    ConversionError(String),

    /// WASI error
    #[error("WASI error: {0}")]
    WasiError(String),

    /// I/O error
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),

    /// Module cache error
    #[error("Module cache error: {0}")]
    CacheError(String),

    /// Invalid WASM binary
    #[error("Invalid WASM binary: {0}")]
    InvalidBinary(String),

    /// Runtime error
    #[error("WASM runtime error: {0}")]
    RuntimeError(String),
}
