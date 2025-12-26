//! Database connection trait and types.

use crate::error::{DbError, DbResult};
use crate::row::Rows;
use crate::transaction::Transaction;
use crate::types::SqlValue;

/// Database connection trait - implemented by all drivers.
pub trait Connection: Send + Sync {
    /// Execute a query that returns rows.
    fn query(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows>;

    /// Execute a query that doesn't return rows (INSERT, UPDATE, DELETE).
    /// Returns the number of affected rows.
    fn execute(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64>;

    /// Begin a transaction.
    fn begin(&self) -> DbResult<Transaction<'_>>;

    /// Check if connection is alive.
    fn ping(&self) -> DbResult<()>;

    /// Close the connection.
    fn close(&mut self) -> DbResult<()>;

    /// Get the driver name.
    fn driver_name(&self) -> &str;
}

/// Database handle for connecting to different backends.
pub struct Database {
    inner: Box<dyn Connection>,
}

impl Database {
    /// Open a database connection.
    ///
    /// Supports the following URL formats:
    /// - `sqlite:./path/to/db.sqlite` or `./path/to/db.db` - Local SQLite/libSQL
    /// - `:memory:` - In-memory SQLite database
    /// - `libsql://host.turso.io?authToken=xxx` - Turso remote database
    /// - `postgres://user:pass@host/db` - PostgreSQL
    pub fn open(url: &str) -> DbResult<Self> {
        let url = url.trim();

        // In-memory SQLite
        if url == ":memory:" {
            return Self::open_libsql_memory();
        }

        // Parse URL scheme
        if let Some(rest) = url.strip_prefix("sqlite:") {
            return Self::open_libsql_local(rest);
        }

        if let Some(rest) = url.strip_prefix("libsql://") {
            return Self::open_libsql_remote(rest);
        }

        if url.starts_with("postgres://") || url.starts_with("postgresql://") {
            return Self::open_postgres(url);
        }

        // Default: treat as local file path
        if url.ends_with(".db") || url.ends_with(".sqlite") || url.ends_with(".sqlite3") {
            return Self::open_libsql_local(url);
        }

        Err(DbError::InvalidUrl(format!("Unknown database URL format: {}", url)))
    }

    /// Open a local libSQL/SQLite database.
    #[cfg(feature = "libsql")]
    fn open_libsql_local(path: &str) -> DbResult<Self> {
        let conn = crate::drivers::libsql::LibsqlConnection::open_local(path)?;
        Ok(Self { inner: Box::new(conn) })
    }

    #[cfg(not(feature = "libsql"))]
    fn open_libsql_local(_path: &str) -> DbResult<Self> {
        Err(DbError::DriverNotAvailable("libsql".to_string()))
    }

    /// Open an in-memory libSQL database.
    #[cfg(feature = "libsql")]
    fn open_libsql_memory() -> DbResult<Self> {
        let conn = crate::drivers::libsql::LibsqlConnection::open_memory()?;
        Ok(Self { inner: Box::new(conn) })
    }

    #[cfg(not(feature = "libsql"))]
    fn open_libsql_memory() -> DbResult<Self> {
        Err(DbError::DriverNotAvailable("libsql".to_string()))
    }

    /// Open a remote libSQL database (Turso).
    #[cfg(feature = "libsql")]
    fn open_libsql_remote(url: &str) -> DbResult<Self> {
        // Parse URL and auth token
        let full_url = format!("libsql://{}", url);
        let (base_url, auth_token) = parse_libsql_url(&full_url)?;
        let conn = crate::drivers::libsql::LibsqlConnection::open_remote(&base_url, &auth_token)?;
        Ok(Self { inner: Box::new(conn) })
    }

    #[cfg(not(feature = "libsql"))]
    fn open_libsql_remote(_url: &str) -> DbResult<Self> {
        Err(DbError::DriverNotAvailable("libsql".to_string()))
    }

    /// Open a PostgreSQL database.
    #[cfg(feature = "postgres")]
    fn open_postgres(url: &str) -> DbResult<Self> {
        let conn = crate::drivers::postgres::PostgresConnection::connect_sync(url)?;
        Ok(Self { inner: Box::new(conn) })
    }

    #[cfg(not(feature = "postgres"))]
    fn open_postgres(_url: &str) -> DbResult<Self> {
        Err(DbError::DriverNotAvailable("postgres".to_string()))
    }

    /// Execute a query that returns rows.
    pub fn query(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        self.inner.query(sql, params)
    }

    /// Execute a query that doesn't return rows.
    pub fn execute(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        self.inner.execute(sql, params)
    }

    /// Begin a transaction.
    pub fn begin(&self) -> DbResult<Transaction<'_>> {
        self.inner.begin()
    }

    /// Check if connection is alive.
    pub fn ping(&self) -> DbResult<()> {
        self.inner.ping()
    }

    /// Get the driver name.
    pub fn driver_name(&self) -> &str {
        self.inner.driver_name()
    }
}

/// Parse libSQL remote URL and extract auth token.
#[cfg(feature = "libsql")]
fn parse_libsql_url(url: &str) -> DbResult<(String, String)> {
    // URL format: libsql://host.turso.io?authToken=xxx
    if let Some(idx) = url.find("?authToken=") {
        let base_url = url[..idx].to_string();
        let auth_token = url[idx + 11..].to_string();
        Ok((base_url, auth_token))
    } else {
        Err(DbError::InvalidUrl(
            "libSQL remote URL must include ?authToken=xxx".to_string()
        ))
    }
}
