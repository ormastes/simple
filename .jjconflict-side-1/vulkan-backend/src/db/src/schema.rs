//! Database schema introspection.
//!
//! Provides unified access to database metadata (tables, columns, indexes, etc.)
//! across different backends.

use crate::error::{DbError, DbResult};
use crate::Connection;

/// Column data type (normalized across databases).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColumnType {
    /// Integer types (SMALLINT, INT, BIGINT, etc.)
    Integer,
    /// Floating-point types (REAL, FLOAT, DOUBLE)
    Real,
    /// Text/string types (TEXT, VARCHAR, CHAR)
    Text,
    /// Binary data (BLOB, BYTEA)
    Blob,
    /// Boolean type
    Boolean,
    /// Date type
    Date,
    /// Time type
    Time,
    /// Timestamp/datetime type
    Timestamp,
    /// JSON type
    Json,
    /// UUID type
    Uuid,
    /// Unknown or custom type
    Unknown(String),
}

impl ColumnType {
    /// Parse from SQLite/libSQL type name.
    pub fn from_sqlite(type_name: &str) -> Self {
        let upper = type_name.to_uppercase();
        match upper.as_str() {
            "INTEGER" | "INT" | "SMALLINT" | "BIGINT" | "TINYINT" => ColumnType::Integer,
            "REAL" | "FLOAT" | "DOUBLE" => ColumnType::Real,
            "TEXT" | "VARCHAR" | "CHAR" | "CLOB" => ColumnType::Text,
            "BLOB" => ColumnType::Blob,
            "BOOLEAN" | "BOOL" => ColumnType::Boolean,
            "DATE" => ColumnType::Date,
            "TIME" => ColumnType::Time,
            "DATETIME" | "TIMESTAMP" => ColumnType::Timestamp,
            "JSON" => ColumnType::Json,
            _ => ColumnType::Unknown(type_name.to_string()),
        }
    }

    /// Parse from PostgreSQL type name.
    pub fn from_postgres(type_name: &str) -> Self {
        let lower = type_name.to_lowercase();
        match lower.as_str() {
            "int2" | "int4" | "int8" | "smallint" | "integer" | "bigint" | "serial" | "bigserial" => {
                ColumnType::Integer
            }
            "float4" | "float8" | "real" | "double precision" | "numeric" | "decimal" => {
                ColumnType::Real
            }
            "text" | "varchar" | "char" | "character varying" | "character" | "name" => {
                ColumnType::Text
            }
            "bytea" => ColumnType::Blob,
            "bool" | "boolean" => ColumnType::Boolean,
            "date" => ColumnType::Date,
            "time" | "time without time zone" | "time with time zone" => ColumnType::Time,
            "timestamp" | "timestamp without time zone" | "timestamp with time zone" | "timestamptz" => {
                ColumnType::Timestamp
            }
            "json" | "jsonb" => ColumnType::Json,
            "uuid" => ColumnType::Uuid,
            _ => ColumnType::Unknown(type_name.to_string()),
        }
    }
}

/// Column information.
#[derive(Debug, Clone)]
pub struct ColumnInfo {
    /// Column name.
    pub name: String,
    /// Column type.
    pub column_type: ColumnType,
    /// Whether the column is nullable.
    pub nullable: bool,
    /// Whether the column is a primary key.
    pub primary_key: bool,
    /// Default value expression (if any).
    pub default_value: Option<String>,
}

/// Table information.
#[derive(Debug, Clone)]
pub struct TableInfo {
    /// Table name.
    pub name: String,
    /// List of columns.
    pub columns: Vec<ColumnInfo>,
    /// Primary key column names.
    pub primary_key: Vec<String>,
}

/// Index information.
#[derive(Debug, Clone)]
pub struct IndexInfo {
    /// Index name.
    pub name: String,
    /// Table the index belongs to.
    pub table_name: String,
    /// Column names in the index.
    pub columns: Vec<String>,
    /// Whether the index is unique.
    pub unique: bool,
}

/// Foreign key information.
#[derive(Debug, Clone)]
pub struct ForeignKeyInfo {
    /// Constraint name (if any).
    pub name: Option<String>,
    /// Source table.
    pub from_table: String,
    /// Source columns.
    pub from_columns: Vec<String>,
    /// Target table.
    pub to_table: String,
    /// Target columns.
    pub to_columns: Vec<String>,
    /// ON DELETE action.
    pub on_delete: String,
    /// ON UPDATE action.
    pub on_update: String,
}

/// Schema introspection trait.
pub trait SchemaIntrospector {
    /// List all table names in the database.
    fn list_tables(&self) -> DbResult<Vec<String>>;

    /// Get information about a specific table.
    fn describe_table(&self, table_name: &str) -> DbResult<TableInfo>;

    /// List all indexes for a table.
    fn list_indexes(&self, table_name: &str) -> DbResult<Vec<IndexInfo>>;

    /// List all foreign keys for a table.
    fn list_foreign_keys(&self, table_name: &str) -> DbResult<Vec<ForeignKeyInfo>>;
}

/// SQLite/libSQL schema introspector.
pub struct SqliteIntrospector<'a, C: Connection + ?Sized> {
    conn: &'a C,
}

impl<'a, C: Connection + ?Sized> SqliteIntrospector<'a, C> {
    /// Create a new SQLite introspector.
    pub fn new(conn: &'a C) -> Self {
        Self { conn }
    }
}

impl<C: Connection + ?Sized> SchemaIntrospector for SqliteIntrospector<'_, C> {
    fn list_tables(&self) -> DbResult<Vec<String>> {
        let rows = self.conn.query(
            "SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' ORDER BY name",
            &[],
        )?;

        let mut tables = Vec::new();
        for row in rows {
            let row = row?;
            if let Some(name) = row.get_opt_by_name::<String>("name")? {
                tables.push(name);
            }
        }
        Ok(tables)
    }

    fn describe_table(&self, table_name: &str) -> DbResult<TableInfo> {
        let rows = self.conn.query(
            &format!("PRAGMA table_info('{}')", table_name.replace('\'', "''")),
            &[],
        )?;

        let mut columns = Vec::new();
        let mut primary_key = Vec::new();

        for row in rows {
            let row = row?;
            let name: String = row.get_by_name("name")?;
            let type_name: String = row.get_opt_by_name("type")?.unwrap_or_default();
            let notnull: i64 = row.get_opt_by_name("notnull")?.unwrap_or(0);
            let pk: i64 = row.get_opt_by_name("pk")?.unwrap_or(0);
            let dflt: Option<String> = row.get_opt_by_name("dflt_value")?;

            let is_pk = pk > 0;
            if is_pk {
                primary_key.push(name.clone());
            }

            columns.push(ColumnInfo {
                name,
                column_type: ColumnType::from_sqlite(&type_name),
                nullable: notnull == 0,
                primary_key: is_pk,
                default_value: dflt,
            });
        }

        if columns.is_empty() {
            return Err(DbError::NotFound(format!("Table '{}' not found", table_name)));
        }

        Ok(TableInfo {
            name: table_name.to_string(),
            columns,
            primary_key,
        })
    }

    fn list_indexes(&self, table_name: &str) -> DbResult<Vec<IndexInfo>> {
        let rows = self.conn.query(
            &format!("PRAGMA index_list('{}')", table_name.replace('\'', "''")),
            &[],
        )?;

        let mut indexes = Vec::new();
        for row in rows {
            let row = row?;
            let name: String = row.get_by_name("name")?;
            let unique: i64 = row.get_opt_by_name("unique")?.unwrap_or(0);

            // Get columns for this index
            let col_rows = self.conn.query(
                &format!("PRAGMA index_info('{}')", name.replace('\'', "''")),
                &[],
            )?;

            let mut columns = Vec::new();
            for col_row in col_rows {
                let col_row = col_row?;
                if let Some(col_name) = col_row.get_opt_by_name::<String>("name")? {
                    columns.push(col_name);
                }
            }

            indexes.push(IndexInfo {
                name,
                table_name: table_name.to_string(),
                columns,
                unique: unique == 1,
            });
        }

        Ok(indexes)
    }

    fn list_foreign_keys(&self, table_name: &str) -> DbResult<Vec<ForeignKeyInfo>> {
        let rows = self.conn.query(
            &format!("PRAGMA foreign_key_list('{}')", table_name.replace('\'', "''")),
            &[],
        )?;

        let mut fks = Vec::new();
        for row in rows {
            let row = row?;
            let to_table: String = row.get_by_name("table")?;
            let from_col: String = row.get_by_name("from")?;
            let to_col: String = row.get_by_name("to")?;
            let on_update: String = row.get_opt_by_name("on_update")?.unwrap_or_else(|| "NO ACTION".to_string());
            let on_delete: String = row.get_opt_by_name("on_delete")?.unwrap_or_else(|| "NO ACTION".to_string());

            fks.push(ForeignKeyInfo {
                name: None,
                from_table: table_name.to_string(),
                from_columns: vec![from_col],
                to_table,
                to_columns: vec![to_col],
                on_delete,
                on_update,
            });
        }

        Ok(fks)
    }
}

/// PostgreSQL schema introspector.
pub struct PostgresIntrospector<'a, C: Connection + ?Sized> {
    conn: &'a C,
}

impl<'a, C: Connection + ?Sized> PostgresIntrospector<'a, C> {
    /// Create a new PostgreSQL introspector.
    pub fn new(conn: &'a C) -> Self {
        Self { conn }
    }
}

impl<C: Connection + ?Sized> SchemaIntrospector for PostgresIntrospector<'_, C> {
    fn list_tables(&self) -> DbResult<Vec<String>> {
        let rows = self.conn.query(
            "SELECT table_name FROM information_schema.tables WHERE table_schema = 'public' ORDER BY table_name",
            &[],
        )?;

        let mut tables = Vec::new();
        for row in rows {
            let row = row?;
            if let Some(name) = row.get_opt_by_name::<String>("table_name")? {
                tables.push(name);
            }
        }
        Ok(tables)
    }

    fn describe_table(&self, table_name: &str) -> DbResult<TableInfo> {
        // Get column information
        let rows = self.conn.query(
            "SELECT column_name, data_type, is_nullable, column_default
             FROM information_schema.columns
             WHERE table_schema = 'public' AND table_name = $1
             ORDER BY ordinal_position",
            &[table_name.into()],
        )?;

        let mut columns = Vec::new();
        for row in rows {
            let row = row?;
            let name: String = row.get_by_name("column_name")?;
            let type_name: String = row.get_opt_by_name("data_type")?.unwrap_or_default();
            let nullable_str: String = row.get_opt_by_name("is_nullable")?.unwrap_or_else(|| "YES".to_string());
            let dflt: Option<String> = row.get_opt_by_name("column_default")?;

            columns.push(ColumnInfo {
                name,
                column_type: ColumnType::from_postgres(&type_name),
                nullable: nullable_str == "YES",
                primary_key: false, // Will be set below
                default_value: dflt,
            });
        }

        if columns.is_empty() {
            return Err(DbError::NotFound(format!("Table '{}' not found", table_name)));
        }

        // Get primary key columns
        let pk_rows = self.conn.query(
            "SELECT kcu.column_name
             FROM information_schema.table_constraints tc
             JOIN information_schema.key_column_usage kcu
               ON tc.constraint_name = kcu.constraint_name AND tc.table_schema = kcu.table_schema
             WHERE tc.constraint_type = 'PRIMARY KEY'
               AND tc.table_schema = 'public' AND tc.table_name = $1
             ORDER BY kcu.ordinal_position",
            &[table_name.into()],
        )?;

        let mut primary_key = Vec::new();
        for pk_row in pk_rows {
            let pk_row = pk_row?;
            if let Some(col_name) = pk_row.get_opt_by_name::<String>("column_name")? {
                primary_key.push(col_name.clone());
                // Mark the column as primary key
                for col in &mut columns {
                    if col.name == col_name {
                        col.primary_key = true;
                    }
                }
            }
        }

        Ok(TableInfo {
            name: table_name.to_string(),
            columns,
            primary_key,
        })
    }

    fn list_indexes(&self, table_name: &str) -> DbResult<Vec<IndexInfo>> {
        let rows = self.conn.query(
            "SELECT i.relname AS index_name, ix.indisunique AS is_unique,
                    array_to_string(array_agg(a.attname ORDER BY k.ordinality), ',') AS columns
             FROM pg_index ix
             JOIN pg_class t ON t.oid = ix.indrelid
             JOIN pg_class i ON i.oid = ix.indexrelid
             JOIN pg_namespace n ON n.oid = t.relnamespace
             JOIN LATERAL unnest(ix.indkey) WITH ORDINALITY AS k(attnum, ordinality) ON true
             JOIN pg_attribute a ON a.attrelid = t.oid AND a.attnum = k.attnum
             WHERE n.nspname = 'public' AND t.relname = $1
             GROUP BY i.relname, ix.indisunique
             ORDER BY i.relname",
            &[table_name.into()],
        )?;

        let mut indexes = Vec::new();
        for row in rows {
            let row = row?;
            let name: String = row.get_by_name("index_name")?;
            let unique: bool = row.get_opt_by_name("is_unique")?.unwrap_or(false);
            let cols_str: String = row.get_opt_by_name("columns")?.unwrap_or_default();

            indexes.push(IndexInfo {
                name,
                table_name: table_name.to_string(),
                columns: cols_str.split(',').map(|s| s.to_string()).collect(),
                unique,
            });
        }

        Ok(indexes)
    }

    fn list_foreign_keys(&self, table_name: &str) -> DbResult<Vec<ForeignKeyInfo>> {
        let rows = self.conn.query(
            "SELECT tc.constraint_name,
                    kcu.column_name AS from_column,
                    ccu.table_name AS to_table,
                    ccu.column_name AS to_column,
                    rc.update_rule,
                    rc.delete_rule
             FROM information_schema.table_constraints tc
             JOIN information_schema.key_column_usage kcu
               ON tc.constraint_name = kcu.constraint_name AND tc.table_schema = kcu.table_schema
             JOIN information_schema.constraint_column_usage ccu
               ON tc.constraint_name = ccu.constraint_name AND tc.table_schema = ccu.table_schema
             JOIN information_schema.referential_constraints rc
               ON tc.constraint_name = rc.constraint_name AND tc.table_schema = rc.constraint_schema
             WHERE tc.constraint_type = 'FOREIGN KEY'
               AND tc.table_schema = 'public' AND tc.table_name = $1",
            &[table_name.into()],
        )?;

        let mut fks = Vec::new();
        for row in rows {
            let row = row?;
            let name: String = row.get_by_name("constraint_name")?;
            let from_col: String = row.get_by_name("from_column")?;
            let to_table: String = row.get_by_name("to_table")?;
            let to_col: String = row.get_by_name("to_column")?;
            let on_update: String = row.get_opt_by_name("update_rule")?.unwrap_or_else(|| "NO ACTION".to_string());
            let on_delete: String = row.get_opt_by_name("delete_rule")?.unwrap_or_else(|| "NO ACTION".to_string());

            fks.push(ForeignKeyInfo {
                name: Some(name),
                from_table: table_name.to_string(),
                from_columns: vec![from_col],
                to_table,
                to_columns: vec![to_col],
                on_delete,
                on_update,
            });
        }

        Ok(fks)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_column_type_from_sqlite() {
        assert_eq!(ColumnType::from_sqlite("INTEGER"), ColumnType::Integer);
        assert_eq!(ColumnType::from_sqlite("TEXT"), ColumnType::Text);
        assert_eq!(ColumnType::from_sqlite("REAL"), ColumnType::Real);
        assert_eq!(ColumnType::from_sqlite("BLOB"), ColumnType::Blob);
        assert_eq!(ColumnType::from_sqlite("BOOLEAN"), ColumnType::Boolean);
    }

    #[test]
    fn test_column_type_from_postgres() {
        assert_eq!(ColumnType::from_postgres("int4"), ColumnType::Integer);
        assert_eq!(ColumnType::from_postgres("text"), ColumnType::Text);
        assert_eq!(ColumnType::from_postgres("float8"), ColumnType::Real);
        assert_eq!(ColumnType::from_postgres("bytea"), ColumnType::Blob);
        assert_eq!(ColumnType::from_postgres("boolean"), ColumnType::Boolean);
        assert_eq!(ColumnType::from_postgres("uuid"), ColumnType::Uuid);
        assert_eq!(ColumnType::from_postgres("jsonb"), ColumnType::Json);
    }

    #[test]
    fn test_column_type_unknown() {
        assert_eq!(
            ColumnType::from_sqlite("CUSTOM_TYPE"),
            ColumnType::Unknown("CUSTOM_TYPE".to_string())
        );
        assert_eq!(
            ColumnType::from_postgres("custom_type"),
            ColumnType::Unknown("custom_type".to_string())
        );
    }
}
