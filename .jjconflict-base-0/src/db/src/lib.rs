//! Database abstraction layer for Simple language.
//!
//! This crate provides a unified interface for database operations across multiple backends:
//! - **libSQL** (SQLite-compatible, local and remote/Turso)
//! - **PostgreSQL** (via native protocol)
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    SQP Layer (Query DSL)                     │
//! ├─────────────────────────────────────────────────────────────┤
//! │                    DB Layer (This Crate)                     │
//! ├─────────────────────┬───────────────────────────────────────┤
//! │   libSQL Driver     │     PostgreSQL Driver                 │
//! └─────────────────────┴───────────────────────────────────────┘
//! ```
//!
//! # Example
//!
//! ```ignore
//! use simple_db::{Database, Connection};
//!
//! // Open a local SQLite database
//! let db = Database::open("./data.db")?;
//!
//! // Execute a query
//! let rows = db.query("SELECT * FROM users WHERE active = ?", &[true.into()])?;
//! for row in rows {
//!     let name: String = row.get("name")?;
//!     println!("User: {}", name);
//! }
//! ```

pub mod connection;
pub mod error;
pub mod pool;
pub mod row;
pub mod schema;
pub mod transaction;
pub mod types;
pub mod drivers;
pub mod ffi;

// Re-export main types
pub use connection::{Connection, Database};
pub use error::{DbError, DbResult};
pub use pool::{Pool, PoolConfig, PoolStats};
pub use row::{Row, Rows};
pub use transaction::{Transaction, Savepoint};
pub use types::{SqlValue, FromSql, ToSql};
pub use schema::{
    ColumnInfo, ColumnType, ForeignKeyInfo, IndexInfo, SchemaIntrospector, TableInfo,
    SqliteIntrospector, PostgresIntrospector,
};

// Re-export FFI functions
pub use ffi::*;
