//! Data Model definitions for SQP.
//!
//! Supports both Casual Mode (convention-based) and Formal Mode (explicit schema).

use std::collections::HashMap;

/// SQL column type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColumnType {
    /// 64-bit integer.
    Integer,
    /// 32-bit integer.
    Int32,
    /// Floating point.
    Float,
    /// Double precision.
    Double,
    /// Text/String.
    Text,
    /// Boolean.
    Boolean,
    /// Date and time.
    DateTime,
    /// Date only.
    Date,
    /// Time only.
    Time,
    /// Binary data.
    Blob,
    /// JSON data.
    Json,
}

impl ColumnType {
    /// Get SQL type name for SQLite.
    pub fn to_sqlite(&self) -> &'static str {
        match self {
            ColumnType::Integer | ColumnType::Int32 => "INTEGER",
            ColumnType::Float | ColumnType::Double => "REAL",
            ColumnType::Text | ColumnType::DateTime | ColumnType::Date | ColumnType::Time => {
                "TEXT"
            }
            ColumnType::Boolean => "INTEGER",
            ColumnType::Blob => "BLOB",
            ColumnType::Json => "TEXT",
        }
    }

    /// Get SQL type name for PostgreSQL.
    pub fn to_postgres(&self) -> &'static str {
        match self {
            ColumnType::Integer => "BIGINT",
            ColumnType::Int32 => "INTEGER",
            ColumnType::Float => "REAL",
            ColumnType::Double => "DOUBLE PRECISION",
            ColumnType::Text => "TEXT",
            ColumnType::Boolean => "BOOLEAN",
            ColumnType::DateTime => "TIMESTAMP",
            ColumnType::Date => "DATE",
            ColumnType::Time => "TIME",
            ColumnType::Blob => "BYTEA",
            ColumnType::Json => "JSONB",
        }
    }
}

/// Column constraint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    /// Primary key.
    PrimaryKey,
    /// Auto-increment primary key.
    AutoIncrement,
    /// Not null.
    NotNull,
    /// Unique.
    Unique,
    /// Default value.
    Default(String),
    /// Check constraint.
    Check(String),
    /// Foreign key reference.
    References { table: String, column: String },
}

/// Column definition.
#[derive(Debug, Clone)]
pub struct Column {
    /// Column name.
    pub name: String,
    /// Column type.
    pub column_type: ColumnType,
    /// SQL column name (may differ from field name).
    pub sql_name: Option<String>,
    /// Constraints.
    pub constraints: Vec<Constraint>,
}

impl Column {
    /// Create a new column definition.
    pub fn new(name: impl Into<String>, column_type: ColumnType) -> Self {
        Self {
            name: name.into(),
            column_type,
            sql_name: None,
            constraints: Vec::new(),
        }
    }

    /// Set the SQL column name.
    pub fn column(mut self, name: impl Into<String>) -> Self {
        self.sql_name = Some(name.into());
        self
    }

    /// Mark as primary key.
    pub fn primary_key(mut self) -> Self {
        self.constraints.push(Constraint::PrimaryKey);
        self
    }

    /// Mark as auto-increment.
    pub fn auto_increment(mut self) -> Self {
        self.constraints.push(Constraint::AutoIncrement);
        self
    }

    /// Mark as not null.
    pub fn not_null(mut self) -> Self {
        self.constraints.push(Constraint::NotNull);
        self
    }

    /// Mark as unique.
    pub fn unique(mut self) -> Self {
        self.constraints.push(Constraint::Unique);
        self
    }

    /// Set default value.
    pub fn default(mut self, value: impl Into<String>) -> Self {
        self.constraints.push(Constraint::Default(value.into()));
        self
    }

    /// Add check constraint.
    pub fn check(mut self, expr: impl Into<String>) -> Self {
        self.constraints.push(Constraint::Check(expr.into()));
        self
    }

    /// Add foreign key reference.
    pub fn references(mut self, table: impl Into<String>, column: impl Into<String>) -> Self {
        self.constraints.push(Constraint::References {
            table: table.into(),
            column: column.into(),
        });
        self
    }

    /// Get the effective SQL column name.
    pub fn sql_column_name(&self) -> &str {
        self.sql_name.as_deref().unwrap_or(&self.name)
    }

    /// Check if column is primary key.
    pub fn is_primary_key(&self) -> bool {
        self.constraints
            .iter()
            .any(|c| matches!(c, Constraint::PrimaryKey | Constraint::AutoIncrement))
    }

    /// Check if column is not null.
    pub fn is_not_null(&self) -> bool {
        self.constraints.iter().any(|c| matches!(c, Constraint::NotNull))
            || self.is_primary_key()
    }

    /// Check if column is unique.
    pub fn is_unique(&self) -> bool {
        self.constraints.iter().any(|c| matches!(c, Constraint::Unique))
            || self.is_primary_key()
    }
}

/// Relationship type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationType {
    /// One-to-many (parent has many children).
    HasMany,
    /// Many-to-one (child belongs to parent).
    BelongsTo,
    /// One-to-one.
    HasOne,
    /// Many-to-many via join table.
    ManyToMany { join_table: String },
}

/// Relationship definition.
#[derive(Debug, Clone)]
pub struct Relation {
    /// Relation name (field name).
    pub name: String,
    /// Related model name.
    pub related_model: String,
    /// Relationship type.
    pub relation_type: RelationType,
    /// Foreign key column name.
    pub foreign_key: String,
    /// Optional: local key column (default: "id").
    pub local_key: String,
}

impl Relation {
    /// Create a has_many relationship.
    pub fn has_many(name: impl Into<String>, model: impl Into<String>) -> Self {
        let name = name.into();
        let model = model.into();
        let fk = crate::naming::to_foreign_key(&model);
        Self {
            name,
            related_model: model,
            relation_type: RelationType::HasMany,
            foreign_key: fk,
            local_key: "id".to_string(),
        }
    }

    /// Create a belongs_to relationship.
    pub fn belongs_to(name: impl Into<String>, model: impl Into<String>) -> Self {
        let name = name.into();
        let model = model.into();
        let fk = crate::naming::to_foreign_key(&model);
        Self {
            name,
            related_model: model,
            relation_type: RelationType::BelongsTo,
            foreign_key: fk,
            local_key: "id".to_string(),
        }
    }

    /// Create a has_one relationship.
    pub fn has_one(name: impl Into<String>, model: impl Into<String>) -> Self {
        let name = name.into();
        let model = model.into();
        let fk = crate::naming::to_foreign_key(&model);
        Self {
            name,
            related_model: model,
            relation_type: RelationType::HasOne,
            foreign_key: fk,
            local_key: "id".to_string(),
        }
    }

    /// Create a many_to_many relationship.
    pub fn many_to_many(
        name: impl Into<String>,
        model: impl Into<String>,
        join_table: impl Into<String>,
    ) -> Self {
        let name = name.into();
        let model = model.into();
        let fk = crate::naming::to_foreign_key(&model);
        Self {
            name,
            related_model: model,
            relation_type: RelationType::ManyToMany {
                join_table: join_table.into(),
            },
            foreign_key: fk,
            local_key: "id".to_string(),
        }
    }

    /// Set custom foreign key.
    pub fn foreign_key(mut self, key: impl Into<String>) -> Self {
        self.foreign_key = key.into();
        self
    }

    /// Set custom local key.
    pub fn local_key(mut self, key: impl Into<String>) -> Self {
        self.local_key = key.into();
        self
    }
}

/// Index definition.
#[derive(Debug, Clone)]
pub struct Index {
    /// Index name.
    pub name: String,
    /// Indexed columns.
    pub columns: Vec<String>,
    /// Whether the index is unique.
    pub unique: bool,
}

impl Index {
    /// Create a new index.
    pub fn new(name: impl Into<String>, columns: Vec<String>) -> Self {
        Self {
            name: name.into(),
            columns,
            unique: false,
        }
    }

    /// Create a unique index.
    pub fn unique(name: impl Into<String>, columns: Vec<String>) -> Self {
        Self {
            name: name.into(),
            columns,
            unique: true,
        }
    }
}

/// Model definition (supports both Casual and Formal modes).
#[derive(Debug, Clone)]
pub struct ModelDef {
    /// Model name (e.g., "User").
    pub name: String,
    /// Table name (e.g., "users").
    pub table_name: String,
    /// Primary key column name.
    pub primary_key: String,
    /// Column definitions.
    pub columns: Vec<Column>,
    /// Relationships.
    pub relations: Vec<Relation>,
    /// Indexes.
    pub indexes: Vec<Index>,
    /// Whether this is a formal mode model.
    pub formal_mode: bool,
}

impl ModelDef {
    /// Create a new casual mode model (infers table name from model name).
    pub fn casual(name: impl Into<String>) -> Self {
        let name = name.into();
        let table_name = crate::naming::to_table_name(&name);
        Self {
            name,
            table_name,
            primary_key: "id".to_string(),
            columns: vec![Column::new("id", ColumnType::Integer)
                .primary_key()
                .auto_increment()],
            relations: Vec::new(),
            indexes: Vec::new(),
            formal_mode: false,
        }
    }

    /// Create a new formal mode model with explicit table name.
    pub fn formal(name: impl Into<String>, table: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            name,
            table_name: table.into(),
            primary_key: "id".to_string(),
            columns: Vec::new(),
            relations: Vec::new(),
            indexes: Vec::new(),
            formal_mode: true,
        }
    }

    /// Set the primary key column.
    pub fn primary_key(mut self, key: impl Into<String>) -> Self {
        self.primary_key = key.into();
        self
    }

    /// Add a column.
    pub fn column(mut self, column: Column) -> Self {
        self.columns.push(column);
        self
    }

    /// Add a relation.
    pub fn relation(mut self, relation: Relation) -> Self {
        self.relations.push(relation);
        self
    }

    /// Add an index.
    pub fn index(mut self, index: Index) -> Self {
        self.indexes.push(index);
        self
    }

    /// Generate CREATE TABLE SQL.
    pub fn to_create_table_sql(&self, dialect: &str) -> String {
        let mut sql = format!("CREATE TABLE {} (\n", self.table_name);

        let column_defs: Vec<String> = self
            .columns
            .iter()
            .map(|col| {
                let mut def = format!(
                    "    {} {}",
                    col.sql_column_name(),
                    if dialect == "postgres" {
                        col.column_type.to_postgres()
                    } else {
                        col.column_type.to_sqlite()
                    }
                );

                for constraint in &col.constraints {
                    match constraint {
                        Constraint::PrimaryKey => def.push_str(" PRIMARY KEY"),
                        Constraint::AutoIncrement => {
                            if dialect == "postgres" {
                                // PostgreSQL uses SERIAL types
                            } else {
                                def.push_str(" AUTOINCREMENT");
                            }
                        }
                        Constraint::NotNull => def.push_str(" NOT NULL"),
                        Constraint::Unique => def.push_str(" UNIQUE"),
                        Constraint::Default(val) => {
                            def.push_str(&format!(" DEFAULT {}", val));
                        }
                        Constraint::Check(expr) => {
                            def.push_str(&format!(" CHECK ({})", expr));
                        }
                        Constraint::References { table, column } => {
                            def.push_str(&format!(" REFERENCES {}({})", table, column));
                        }
                    }
                }

                def
            })
            .collect();

        sql.push_str(&column_defs.join(",\n"));
        sql.push_str("\n)");

        sql
    }

    /// Generate CREATE INDEX SQL statements.
    pub fn to_create_indexes_sql(&self) -> Vec<String> {
        self.indexes
            .iter()
            .map(|idx| {
                let unique = if idx.unique { "UNIQUE " } else { "" };
                format!(
                    "CREATE {}INDEX {} ON {} ({})",
                    unique,
                    idx.name,
                    self.table_name,
                    idx.columns.join(", ")
                )
            })
            .collect()
    }
}

/// Model registry for storing all model definitions.
#[derive(Debug, Default)]
pub struct ModelRegistry {
    models: HashMap<String, ModelDef>,
}

impl ModelRegistry {
    /// Create a new registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a model.
    pub fn register(&mut self, model: ModelDef) {
        self.models.insert(model.name.clone(), model);
    }

    /// Get a model by name.
    pub fn get(&self, name: &str) -> Option<&ModelDef> {
        self.models.get(name)
    }

    /// Get all models.
    pub fn all(&self) -> impl Iterator<Item = &ModelDef> {
        self.models.values()
    }

    /// Generate SQL for all models.
    pub fn to_schema_sql(&self, dialect: &str) -> String {
        let mut sql = String::new();

        for model in self.models.values() {
            sql.push_str(&model.to_create_table_sql(dialect));
            sql.push_str(";\n\n");

            for idx_sql in model.to_create_indexes_sql() {
                sql.push_str(&idx_sql);
                sql.push_str(";\n");
            }
        }

        sql
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_casual_model() {
        let model = ModelDef::casual("User")
            .column(Column::new("name", ColumnType::Text).not_null())
            .column(Column::new("email", ColumnType::Text).not_null().unique())
            .column(Column::new("age", ColumnType::Int32).default("0"));

        assert_eq!(model.name, "User");
        assert_eq!(model.table_name, "users");
        assert_eq!(model.primary_key, "id");
        assert!(!model.formal_mode);
        assert_eq!(model.columns.len(), 4); // id + 3 columns
    }

    #[test]
    fn test_formal_model() {
        let model = ModelDef::formal("User", "app_users")
            .primary_key("user_id")
            .column(
                Column::new("user_id", ColumnType::Integer)
                    .primary_key()
                    .auto_increment(),
            )
            .column(Column::new("full_name", ColumnType::Text).column("name").not_null());

        assert_eq!(model.name, "User");
        assert_eq!(model.table_name, "app_users");
        assert_eq!(model.primary_key, "user_id");
        assert!(model.formal_mode);
    }

    #[test]
    fn test_has_many_relation() {
        let relation = Relation::has_many("posts", "Post");
        assert_eq!(relation.name, "posts");
        assert_eq!(relation.related_model, "Post");
        assert_eq!(relation.relation_type, RelationType::HasMany);
        assert_eq!(relation.foreign_key, "post_id");
    }

    #[test]
    fn test_belongs_to_relation() {
        let relation = Relation::belongs_to("author", "User").foreign_key("author_id");
        assert_eq!(relation.name, "author");
        assert_eq!(relation.related_model, "User");
        assert_eq!(relation.relation_type, RelationType::BelongsTo);
        assert_eq!(relation.foreign_key, "author_id");
    }

    #[test]
    fn test_create_table_sql() {
        let model = ModelDef::casual("User")
            .column(Column::new("name", ColumnType::Text).not_null())
            .column(Column::new("email", ColumnType::Text).not_null().unique());

        let sql = model.to_create_table_sql("sqlite");
        assert!(sql.contains("CREATE TABLE users"));
        assert!(sql.contains("id INTEGER PRIMARY KEY"));
        assert!(sql.contains("name TEXT NOT NULL"));
        assert!(sql.contains("email TEXT NOT NULL UNIQUE"));
    }

    #[test]
    fn test_index() {
        let model = ModelDef::casual("User")
            .column(Column::new("email", ColumnType::Text))
            .index(Index::unique("idx_email", vec!["email".to_string()]));

        let indexes = model.to_create_indexes_sql();
        assert_eq!(indexes.len(), 1);
        assert!(indexes[0].contains("UNIQUE INDEX"));
        assert!(indexes[0].contains("idx_email"));
    }

    #[test]
    fn test_model_registry() {
        let mut registry = ModelRegistry::new();

        registry.register(ModelDef::casual("User"));
        registry.register(ModelDef::casual("Post"));

        assert!(registry.get("User").is_some());
        assert!(registry.get("Post").is_some());
        assert!(registry.get("Comment").is_none());
    }
}
