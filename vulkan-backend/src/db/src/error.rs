//! Database error types.

use thiserror::Error;

/// Result type for database operations.
pub type DbResult<T> = Result<T, DbError>;

/// Database error type.
#[derive(Error, Debug)]
pub enum DbError {
    /// Connection to database failed
    #[error("connection failed: {0}")]
    ConnectionFailed(String),

    /// Query execution failed
    #[error("query failed: {0}")]
    QueryFailed(String),

    /// Type conversion error
    #[error("type mismatch: expected {expected}, got {got}")]
    TypeMismatch {
        expected: String,
        got: String,
    },

    /// Column not found
    #[error("column not found: {0}")]
    ColumnNotFound(String),

    /// Row not found
    #[error("row not found")]
    RowNotFound,

    /// Resource not found (table, column, etc.)
    #[error("not found: {0}")]
    NotFound(String),

    /// Transaction error
    #[error("transaction failed: {0}")]
    TransactionFailed(String),

    /// Connection pool exhausted
    #[error("connection pool exhausted")]
    PoolExhausted,

    /// Connection was closed
    #[error("connection closed")]
    ConnectionClosed,

    /// Operation timed out
    #[error("operation timed out")]
    Timeout,

    /// Invalid URL format
    #[error("invalid URL: {0}")]
    InvalidUrl(String),

    /// Driver not available
    #[error("driver not available: {0}")]
    DriverNotAvailable(String),

    /// IO error
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    /// Driver-specific error
    #[error("driver error: {0}")]
    Driver(String),

    /// libSQL specific error
    #[cfg(feature = "libsql")]
    #[error("libsql error: {0}")]
    LibSql(#[from] libsql::Error),
}

impl DbError {
    /// Create a connection failed error.
    pub fn connection_failed(msg: impl Into<String>) -> Self {
        Self::ConnectionFailed(msg.into())
    }

    /// Create a query failed error.
    pub fn query_failed(msg: impl Into<String>) -> Self {
        Self::QueryFailed(msg.into())
    }

    /// Create a type mismatch error.
    pub fn type_mismatch(expected: impl Into<String>, got: impl Into<String>) -> Self {
        Self::TypeMismatch {
            expected: expected.into(),
            got: got.into(),
        }
    }

    /// Create a column not found error.
    pub fn column_not_found(name: impl Into<String>) -> Self {
        Self::ColumnNotFound(name.into())
    }

    /// Create a transaction failed error.
    pub fn transaction_failed(msg: impl Into<String>) -> Self {
        Self::TransactionFailed(msg.into())
    }

    /// Create a driver error.
    pub fn driver(msg: impl Into<String>) -> Self {
        Self::Driver(msg.into())
    }
}
