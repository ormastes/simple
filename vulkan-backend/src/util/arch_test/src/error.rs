//! Error types for architecture testing

use thiserror::Error;

/// Architecture test error
#[derive(Debug, Error)]
pub enum ArchError {
    /// I/O error during file operations
    #[error("I/O error: {0}")]
    IoError(String),

    /// Invalid configuration
    #[error("Configuration error: {0}")]
    ConfigError(String),

    /// Rule definition error
    #[error("Rule error: {0}")]
    RuleError(String),

    /// Layer not found
    #[error("Layer not found: {0}")]
    LayerNotFound(String),
}
