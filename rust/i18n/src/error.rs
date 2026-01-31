use thiserror::Error;

#[derive(Error, Debug)]
pub enum I18nError {
    #[error("Failed to load catalog from {path}: {source}")]
    CatalogLoadError { path: String, source: std::io::Error },

    #[error("Failed to parse catalog from {path}: {message}")]
    CatalogParseError { path: String, message: String },

    #[error("Message not found: {domain}.{id}")]
    MessageNotFound { domain: String, id: String },

    #[error("Invalid locale format: {0}")]
    InvalidLocale(String),

    #[error("Catalog directory not found: {0}")]
    CatalogDirectoryNotFound(String),
}

pub type Result<T> = std::result::Result<T, I18nError>;
