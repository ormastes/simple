//! Package manager error types

use thiserror::Error;

/// Package manager error type
#[derive(Error, Debug)]
pub enum PkgError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("TOML parse error: {0}")]
    TomlParse(#[from] toml::de::Error),

    #[error("TOML serialize error: {0}")]
    TomlSerialize(#[from] toml::ser::Error),

    #[error("Invalid version: {0}")]
    InvalidVersion(String),

    #[error("Version parse error: {0}")]
    VersionParse(String),

    #[error("Manifest not found: {0}")]
    ManifestNotFound(String),

    #[error("Invalid manifest: {0}")]
    InvalidManifest(String),

    #[error("Package not found: {0}")]
    PackageNotFound(String),

    #[error("Dependency conflict: {0}")]
    DependencyConflict(String),

    #[error("Circular dependency: {0}")]
    CircularDependency(String),

    #[error("Resolution error: {0}")]
    Resolution(String),

    #[error("Link error: {0}")]
    Link(String),

    #[error("Cache error: {0}")]
    Cache(String),

    #[error("Git error: {0}")]
    Git(String),

    #[error("Already initialized: {0}")]
    AlreadyInitialized(String),

    #[error("{0}")]
    Other(String),
}

/// Result type alias for package operations
pub type PkgResult<T> = Result<T, PkgError>;
