//! libSQL driver implementation (SQLite-compatible).
//!
//! Supports:
//! - Local SQLite files
//! - In-memory databases
//! - Remote Turso databases
//!
//! Note: libsql uses async API internally, so we use a dedicated runtime.

use crate::connection::Connection;
use crate::error::{DbError, DbResult};
use crate::row::{Row, Rows};
use crate::transaction::{Transaction, TransactionExecutor};
use crate::types::SqlValue;

use libsql::{Connection as LibsqlConn, Database, Value as LibsqlValue};
use parking_lot::Mutex;
use std::sync::Arc;

/// libSQL connection.
pub struct LibsqlConnection {
    /// The database handle (kept for potential future use like sync).
    #[allow(dead_code)]
    db: Database,
    /// Current connection.
    conn: Arc<Mutex<LibsqlConn>>,
    /// Tokio runtime for async operations.
    runtime: tokio::runtime::Runtime,
}

impl LibsqlConnection {
    /// Create runtime for async operations.
    fn create_runtime() -> DbResult<tokio::runtime::Runtime> {
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| DbError::connection_failed(e.to_string()))
    }

    /// Open a local SQLite file.
    #[allow(deprecated)]
    pub fn open_local(path: &str) -> DbResult<Self> {
        let runtime = Self::create_runtime()?;
        let (db, conn) = runtime.block_on(async {
            let db = Database::open(path).map_err(|e| DbError::connection_failed(e.to_string()))?;
            let conn = db
                .connect()
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            Ok::<_, DbError>((db, conn))
        })?;
        Ok(Self {
            db,
            conn: Arc::new(Mutex::new(conn)),
            runtime,
        })
    }

    /// Open an in-memory database.
    #[allow(deprecated)]
    pub fn open_memory() -> DbResult<Self> {
        let runtime = Self::create_runtime()?;
        let (db, conn) = runtime.block_on(async {
            let db = Database::open(":memory:")
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            let conn = db
                .connect()
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            Ok::<_, DbError>((db, conn))
        })?;
        Ok(Self {
            db,
            conn: Arc::new(Mutex::new(conn)),
            runtime,
        })
    }

    /// Open a remote Turso database.
    #[allow(deprecated)]
    pub fn open_remote(url: &str, auth_token: &str) -> DbResult<Self> {
        let runtime = Self::create_runtime()?;
        let (db, conn) = runtime.block_on(async {
            let db = Database::open_remote(url, auth_token)
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            let conn = db
                .connect()
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            Ok::<_, DbError>((db, conn))
        })?;
        Ok(Self {
            db,
            conn: Arc::new(Mutex::new(conn)),
            runtime,
        })
    }

    /// Open with embedded replica (local cache + remote sync).
    #[allow(deprecated)]
    pub fn open_replica(path: &str, url: &str, auth_token: &str) -> DbResult<Self> {
        let runtime = Self::create_runtime()?;
        let (db, conn) = runtime.block_on(async {
            let db = Database::open_with_remote_sync(path, url, auth_token, None)
                .await
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            let conn = db
                .connect()
                .map_err(|e| DbError::connection_failed(e.to_string()))?;
            Ok::<_, DbError>((db, conn))
        })?;
        Ok(Self {
            db,
            conn: Arc::new(Mutex::new(conn)),
            runtime,
        })
    }

    /// Internal query implementation.
    fn query_internal(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        let conn = self.conn.lock();
        let libsql_params: Vec<LibsqlValue> = params.iter().map(to_libsql_value).collect();

        // Use block_on for async operations
        let result = self.runtime.block_on(async {
            let mut rows = conn
                .query(sql, libsql_params)
                .await
                .map_err(|e| DbError::query_failed(e.to_string()))?;

            // Get column count
            let column_count = rows.column_count();

            // Get column names
            let columns: Vec<String> = (0..column_count)
                .map(|i| {
                    rows.column_name(i)
                        .map(|s| s.to_string())
                        .unwrap_or_default()
                })
                .collect();

            // Collect all rows
            let mut row_vec: Vec<DbResult<Row>> = Vec::new();
            loop {
                match rows.next().await {
                    Ok(Some(row)) => {
                        let values: Vec<SqlValue> = (0..column_count)
                            .map(|i| {
                                let value = row.get_value(i).unwrap_or(LibsqlValue::Null);
                                from_libsql_value(value)
                            })
                            .collect();
                        row_vec.push(Ok(Row::new(values, columns.clone())));
                    }
                    Ok(None) => break,
                    Err(e) => {
                        row_vec.push(Err(DbError::query_failed(e.to_string())));
                        break;
                    }
                }
            }

            Ok::<_, DbError>((row_vec, columns))
        })?;

        let (rows_vec, columns) = result;
        Ok(Rows::new(Box::new(rows_vec.into_iter()), columns))
    }

    /// Internal execute implementation.
    fn execute_internal(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        let conn = self.conn.lock();
        let libsql_params: Vec<LibsqlValue> = params.iter().map(to_libsql_value).collect();

        self.runtime.block_on(async {
            conn.execute(sql, libsql_params)
                .await
                .map_err(|e| DbError::query_failed(e.to_string()))
        })
    }
}

impl Connection for LibsqlConnection {
    fn query(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        self.query_internal(sql, params)
    }

    fn execute(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        self.execute_internal(sql, params)
    }

    fn begin(&self) -> DbResult<Transaction<'_>> {
        Transaction::new(self)
    }

    fn ping(&self) -> DbResult<()> {
        self.execute("SELECT 1", &[])?;
        Ok(())
    }

    fn close(&mut self) -> DbResult<()> {
        // libSQL connections are automatically closed when dropped
        Ok(())
    }

    fn driver_name(&self) -> &str {
        "libsql"
    }
}

impl TransactionExecutor for LibsqlConnection {
    fn execute_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        self.execute(sql, params)
    }

    fn query_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        self.query(sql, params)
    }
}

/// Convert SqlValue to libSQL Value.
fn to_libsql_value(value: &SqlValue) -> LibsqlValue {
    match value {
        SqlValue::Null => LibsqlValue::Null,
        SqlValue::Integer(i) => LibsqlValue::Integer(*i),
        SqlValue::Real(f) => LibsqlValue::Real(*f),
        SqlValue::Text(s) => LibsqlValue::Text(s.clone()),
        SqlValue::Blob(b) => LibsqlValue::Blob(b.clone()),
        SqlValue::Boolean(b) => LibsqlValue::Integer(if *b { 1 } else { 0 }),
    }
}

/// Convert libSQL Value to SqlValue.
fn from_libsql_value(value: LibsqlValue) -> SqlValue {
    match value {
        LibsqlValue::Null => SqlValue::Null,
        LibsqlValue::Integer(i) => SqlValue::Integer(i),
        LibsqlValue::Real(f) => SqlValue::Real(f),
        LibsqlValue::Text(s) => SqlValue::Text(s),
        LibsqlValue::Blob(b) => SqlValue::Blob(b),
    }
}

// Make LibsqlConnection Send + Sync
unsafe impl Send for LibsqlConnection {}
unsafe impl Sync for LibsqlConnection {}
