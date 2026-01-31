//! Database migrations for SQP.
//!
//! Provides schema versioning and evolution.

use std::collections::BTreeMap;

use crate::model::{Column, ColumnType};

/// Migration direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Apply migration (up).
    Up,
    /// Rollback migration (down).
    Down,
}

/// A single migration operation.
#[derive(Debug, Clone)]
pub enum Operation {
    /// Create a new table.
    CreateTable { name: String, columns: Vec<Column> },
    /// Drop a table.
    DropTable { name: String },
    /// Add a column to a table.
    AddColumn { table: String, column: Column },
    /// Drop a column from a table.
    DropColumn { table: String, column: String },
    /// Rename a column.
    RenameColumn { table: String, from: String, to: String },
    /// Change column type.
    ChangeColumn {
        table: String,
        column: String,
        new_type: ColumnType,
        nullable: bool,
    },
    /// Create an index.
    CreateIndex {
        name: String,
        table: String,
        columns: Vec<String>,
        unique: bool,
    },
    /// Drop an index.
    DropIndex { name: String, table: String },
    /// Add a foreign key.
    AddForeignKey {
        name: String,
        table: String,
        column: String,
        references_table: String,
        references_column: String,
        on_delete: Option<String>,
    },
    /// Remove a foreign key.
    RemoveForeignKey { name: String, table: String },
    /// Execute raw SQL.
    RawSql(String),
}

impl Operation {
    /// Generate SQL for this operation.
    pub fn to_sql(&self, dialect: &str) -> String {
        match self {
            Operation::CreateTable { name, columns } => {
                let col_defs: Vec<String> = columns
                    .iter()
                    .map(|c| {
                        let type_str = if dialect == "postgres" {
                            c.column_type.to_postgres()
                        } else {
                            c.column_type.to_sqlite()
                        };
                        let mut def = format!("{} {}", c.sql_column_name(), type_str);
                        if c.is_primary_key() {
                            def.push_str(" PRIMARY KEY");
                        }
                        if c.is_not_null() && !c.is_primary_key() {
                            def.push_str(" NOT NULL");
                        }
                        def
                    })
                    .collect();
                format!("CREATE TABLE {} (\n  {}\n)", name, col_defs.join(",\n  "))
            }
            Operation::DropTable { name } => {
                format!("DROP TABLE {}", name)
            }
            Operation::AddColumn { table, column } => {
                let type_str = if dialect == "postgres" {
                    column.column_type.to_postgres()
                } else {
                    column.column_type.to_sqlite()
                };
                let mut def = format!(
                    "ALTER TABLE {} ADD COLUMN {} {}",
                    table,
                    column.sql_column_name(),
                    type_str
                );
                if column.is_not_null() {
                    def.push_str(" NOT NULL");
                }
                def
            }
            Operation::DropColumn { table, column } => {
                format!("ALTER TABLE {} DROP COLUMN {}", table, column)
            }
            Operation::RenameColumn { table, from, to } => {
                if dialect == "postgres" {
                    format!("ALTER TABLE {} RENAME COLUMN {} TO {}", table, from, to)
                } else {
                    // SQLite 3.25+ supports this
                    format!("ALTER TABLE {} RENAME COLUMN {} TO {}", table, from, to)
                }
            }
            Operation::ChangeColumn {
                table,
                column,
                new_type,
                nullable,
            } => {
                let type_str = if dialect == "postgres" {
                    new_type.to_postgres()
                } else {
                    new_type.to_sqlite()
                };
                if dialect == "postgres" {
                    let mut sql = format!("ALTER TABLE {} ALTER COLUMN {} TYPE {}", table, column, type_str);
                    if !nullable {
                        sql.push_str(&format!("; ALTER TABLE {} ALTER COLUMN {} SET NOT NULL", table, column));
                    }
                    sql
                } else {
                    // SQLite doesn't support ALTER COLUMN well; requires table rebuild
                    format!(
                        "-- SQLite: Column type change requires table rebuild for {} {}",
                        table, column
                    )
                }
            }
            Operation::CreateIndex {
                name,
                table,
                columns,
                unique,
            } => {
                let unique_str = if *unique { "UNIQUE " } else { "" };
                format!(
                    "CREATE {}INDEX {} ON {} ({})",
                    unique_str,
                    name,
                    table,
                    columns.join(", ")
                )
            }
            Operation::DropIndex { name, table: _ } => {
                if dialect == "postgres" {
                    format!("DROP INDEX {}", name)
                } else {
                    format!("DROP INDEX IF EXISTS {}", name)
                }
            }
            Operation::AddForeignKey {
                name,
                table,
                column,
                references_table,
                references_column,
                on_delete,
            } => {
                let mut sql = format!(
                    "ALTER TABLE {} ADD CONSTRAINT {} FOREIGN KEY ({}) REFERENCES {}({})",
                    table, name, column, references_table, references_column
                );
                if let Some(action) = on_delete {
                    sql.push_str(&format!(" ON DELETE {}", action));
                }
                sql
            }
            Operation::RemoveForeignKey { name, table } => {
                if dialect == "postgres" {
                    format!("ALTER TABLE {} DROP CONSTRAINT {}", table, name)
                } else {
                    // SQLite doesn't support dropping foreign keys
                    format!("-- SQLite: Cannot drop foreign key {}; requires table rebuild", name)
                }
            }
            Operation::RawSql(sql) => sql.clone(),
        }
    }
}

/// A database migration.
#[derive(Debug, Clone)]
pub struct Migration {
    /// Migration version/name (e.g., "001_create_users").
    pub version: String,
    /// Up operations (apply migration).
    pub up: Vec<Operation>,
    /// Down operations (rollback migration).
    pub down: Vec<Operation>,
}

impl Migration {
    /// Create a new migration.
    pub fn new(version: impl Into<String>) -> Self {
        Self {
            version: version.into(),
            up: Vec::new(),
            down: Vec::new(),
        }
    }

    /// Add an up operation.
    pub fn up_op(mut self, op: Operation) -> Self {
        self.up.push(op);
        self
    }

    /// Add a down operation.
    pub fn down_op(mut self, op: Operation) -> Self {
        self.down.push(op);
        self
    }

    /// Create table helper.
    pub fn create_table(mut self, name: impl Into<String>, columns: Vec<Column>) -> Self {
        let name = name.into();
        self.up.push(Operation::CreateTable {
            name: name.clone(),
            columns,
        });
        self.down.push(Operation::DropTable { name });
        self
    }

    /// Drop table helper.
    pub fn drop_table(mut self, name: impl Into<String>) -> Self {
        self.down.push(Operation::DropTable { name: name.into() });
        self
    }

    /// Add column helper.
    pub fn add_column(mut self, table: impl Into<String>, column: Column) -> Self {
        let table = table.into();
        let col_name = column.name.clone();
        self.up.push(Operation::AddColumn {
            table: table.clone(),
            column,
        });
        self.down.push(Operation::DropColumn {
            table,
            column: col_name,
        });
        self
    }

    /// Create index helper.
    pub fn create_index(
        mut self,
        name: impl Into<String>,
        table: impl Into<String>,
        columns: Vec<String>,
        unique: bool,
    ) -> Self {
        let name = name.into();
        let table = table.into();
        self.up.push(Operation::CreateIndex {
            name: name.clone(),
            table: table.clone(),
            columns,
            unique,
        });
        self.down.push(Operation::DropIndex { name, table });
        self
    }

    /// Generate up SQL.
    pub fn up_sql(&self, dialect: &str) -> Vec<String> {
        self.up.iter().map(|op| op.to_sql(dialect)).collect()
    }

    /// Generate down SQL.
    pub fn down_sql(&self, dialect: &str) -> Vec<String> {
        self.down.iter().rev().map(|op| op.to_sql(dialect)).collect()
    }
}

/// Migration status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MigrationStatus {
    /// Migration has been applied.
    Applied,
    /// Migration is pending.
    Pending,
}

/// Migration record (stored in database).
#[derive(Debug, Clone)]
pub struct MigrationRecord {
    /// Migration version.
    pub version: String,
    /// When the migration was applied.
    pub applied_at: String,
}

/// Migration runner.
#[derive(Debug, Default)]
pub struct Migrator {
    /// All registered migrations.
    migrations: BTreeMap<String, Migration>,
    /// Applied migrations (loaded from database).
    applied: Vec<String>,
}

impl Migrator {
    /// Create a new migrator.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a migration.
    pub fn register(&mut self, migration: Migration) {
        self.migrations.insert(migration.version.clone(), migration);
    }

    /// Set applied migrations (loaded from database).
    pub fn set_applied(&mut self, versions: Vec<String>) {
        self.applied = versions;
    }

    /// Get pending migrations.
    pub fn pending(&self) -> Vec<&Migration> {
        self.migrations
            .values()
            .filter(|m| !self.applied.contains(&m.version))
            .collect()
    }

    /// Get applied migrations.
    pub fn applied(&self) -> Vec<&Migration> {
        self.applied.iter().filter_map(|v| self.migrations.get(v)).collect()
    }

    /// Get migration status.
    pub fn status(&self) -> Vec<(&Migration, MigrationStatus)> {
        self.migrations
            .values()
            .map(|m| {
                let status = if self.applied.contains(&m.version) {
                    MigrationStatus::Applied
                } else {
                    MigrationStatus::Pending
                };
                (m, status)
            })
            .collect()
    }

    /// Generate SQL for running all pending migrations.
    pub fn pending_sql(&self, dialect: &str) -> Vec<(String, Vec<String>)> {
        self.pending()
            .into_iter()
            .map(|m| (m.version.clone(), m.up_sql(dialect)))
            .collect()
    }

    /// Generate SQL for rolling back N migrations.
    pub fn rollback_sql(&self, dialect: &str, count: usize) -> Vec<(String, Vec<String>)> {
        self.applied()
            .into_iter()
            .rev()
            .take(count)
            .map(|m| (m.version.clone(), m.down_sql(dialect)))
            .collect()
    }

    /// SQL to create the migrations tracking table.
    pub fn create_migrations_table_sql(&self, table_name: &str) -> String {
        format!(
            "CREATE TABLE IF NOT EXISTS {} (\n  version TEXT PRIMARY KEY,\n  applied_at TEXT NOT NULL\n)",
            table_name
        )
    }

    /// SQL to record a migration as applied.
    pub fn record_migration_sql(&self, table_name: &str, version: &str) -> String {
        format!(
            "INSERT INTO {} (version, applied_at) VALUES ('{}', datetime('now'))",
            table_name, version
        )
    }

    /// SQL to remove a migration record.
    pub fn remove_migration_sql(&self, table_name: &str, version: &str) -> String {
        format!("DELETE FROM {} WHERE version = '{}'", table_name, version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_table_operation() {
        let op = Operation::CreateTable {
            name: "users".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer).primary_key().auto_increment(),
                Column::new("name", ColumnType::Text).not_null(),
            ],
        };

        let sql = op.to_sql("sqlite");
        assert!(sql.contains("CREATE TABLE users"));
        assert!(sql.contains("id INTEGER PRIMARY KEY"));
        assert!(sql.contains("name TEXT NOT NULL"));
    }

    #[test]
    fn test_migration() {
        let migration = Migration::new("001_create_users").create_table(
            "users",
            vec![
                Column::new("id", ColumnType::Integer).primary_key().auto_increment(),
                Column::new("name", ColumnType::Text).not_null(),
            ],
        );

        assert_eq!(migration.version, "001_create_users");
        assert_eq!(migration.up.len(), 1);
        assert_eq!(migration.down.len(), 1);

        let up_sql = migration.up_sql("sqlite");
        assert_eq!(up_sql.len(), 1);
        assert!(up_sql[0].contains("CREATE TABLE users"));

        let down_sql = migration.down_sql("sqlite");
        assert_eq!(down_sql.len(), 1);
        assert!(down_sql[0].contains("DROP TABLE users"));
    }

    #[test]
    fn test_add_column_migration() {
        let migration =
            Migration::new("002_add_email").add_column("users", Column::new("email", ColumnType::Text).not_null());

        let up_sql = migration.up_sql("sqlite");
        assert!(up_sql[0].contains("ADD COLUMN email"));

        let down_sql = migration.down_sql("sqlite");
        assert!(down_sql[0].contains("DROP COLUMN email"));
    }

    #[test]
    fn test_create_index_migration() {
        let migration = Migration::new("003_add_email_index").create_index(
            "idx_users_email",
            "users",
            vec!["email".to_string()],
            true,
        );

        let up_sql = migration.up_sql("sqlite");
        assert!(up_sql[0].contains("CREATE UNIQUE INDEX"));

        let down_sql = migration.down_sql("sqlite");
        assert!(down_sql[0].contains("DROP INDEX"));
    }

    #[test]
    fn test_migrator() {
        let mut migrator = Migrator::new();

        migrator.register(Migration::new("001_create_users"));
        migrator.register(Migration::new("002_add_email"));
        migrator.register(Migration::new("003_add_index"));

        assert_eq!(migrator.pending().len(), 3);

        migrator.set_applied(vec!["001_create_users".to_string()]);

        assert_eq!(migrator.pending().len(), 2);
        assert_eq!(migrator.applied().len(), 1);

        let status = migrator.status();
        assert_eq!(status.len(), 3);
    }

    #[test]
    fn test_postgres_operations() {
        let op = Operation::CreateTable {
            name: "users".to_string(),
            columns: vec![
                Column::new("id", ColumnType::Integer).primary_key(),
                Column::new("created_at", ColumnType::DateTime).not_null(),
            ],
        };

        let sql = op.to_sql("postgres");
        assert!(sql.contains("BIGINT"));
        assert!(sql.contains("TIMESTAMP"));
    }
}
