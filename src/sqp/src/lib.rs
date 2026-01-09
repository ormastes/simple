//! Simple Query and Persistence (SQP) layer.
//!
//! SQP provides a high-level query DSL and ORM-like data modeling for Simple language.
//!
//! # Features
//!
//! - **Query DSL**: Type-safe, chainable query builder
//! - **Raw SQL**: Escape hatch for complex queries
//! - **Naming conventions**: Automatic table/column name conversion
//!
//! # Example
//!
//! ```ignore
//! use simple_sqp::{Query, Condition};
//!
//! let query = Query::table("users")
//!     .select(&["id", "name", "email"])
//!     .where_(Condition::eq("status", "active"))
//!     .where_(Condition::gt("age", 18))
//!     .order_by("name", Order::Asc)
//!     .limit(10);
//!
//! let (sql, params) = query.build();
//! // sql = "SELECT id, name, email FROM users WHERE status = ? AND age > ? ORDER BY name ASC LIMIT 10"
//! // params = ["active", 18]
//! ```

pub mod condition;
pub mod migration;
pub mod model;
pub mod naming;
pub mod preload;
pub mod query;
pub mod raw;

// Re-exports
pub use condition::{Condition, Op};
pub use naming::{to_column_name, to_foreign_key, to_table_name};
pub use query::{JoinType, Order, Query};
pub use raw::RawSql;

// Model re-exports
pub use model::{
    Column, ColumnType, Constraint, Index, ModelDef, ModelRegistry, Relation, RelationType,
};

// Migration re-exports
pub use migration::{Direction, Migration, MigrationRecord, MigrationStatus, Migrator, Operation};

// Preload re-exports
pub use preload::{
    group_by_foreign_key, parse_preload, Preload, PreloadBuilder, PreloadConfig, PreloadQuery,
    PreloadStrategy,
};
