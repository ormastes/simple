//! Query conditions and operators.

use simple_db::SqlValue;

/// Comparison operator.
#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    /// Equal (=)
    Eq,
    /// Not equal (!=)
    Ne,
    /// Greater than (>)
    Gt,
    /// Greater than or equal (>=)
    Gte,
    /// Less than (<)
    Lt,
    /// Less than or equal (<=)
    Lte,
    /// LIKE pattern
    Like,
    /// NOT LIKE pattern
    NotLike,
    /// IN list
    In,
    /// NOT IN list
    NotIn,
    /// IS NULL
    IsNull,
    /// IS NOT NULL
    IsNotNull,
    /// BETWEEN
    Between,
}

/// A query condition.
#[derive(Debug, Clone)]
pub enum Condition {
    /// Simple comparison (column op value)
    Compare {
        column: String,
        op: Op,
        value: SqlValue,
    },
    /// IN or NOT IN with multiple values
    InList {
        column: String,
        values: Vec<SqlValue>,
        negated: bool,
    },
    /// BETWEEN two values
    Between {
        column: String,
        low: SqlValue,
        high: SqlValue,
    },
    /// IS NULL or IS NOT NULL
    Null { column: String, is_null: bool },
    /// AND of multiple conditions
    And(Vec<Condition>),
    /// OR of multiple conditions
    Or(Vec<Condition>),
    /// NOT condition
    Not(Box<Condition>),
    /// Raw SQL condition
    Raw { sql: String, params: Vec<SqlValue> },
}

impl Condition {
    /// Create an equality condition (column = value).
    pub fn eq(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Eq,
            value: value.into(),
        }
    }

    /// Create a not-equal condition (column != value).
    pub fn ne(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Ne,
            value: value.into(),
        }
    }

    /// Create a greater-than condition (column > value).
    pub fn gt(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Gt,
            value: value.into(),
        }
    }

    /// Create a greater-than-or-equal condition (column >= value).
    pub fn gte(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Gte,
            value: value.into(),
        }
    }

    /// Create a less-than condition (column < value).
    pub fn lt(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Lt,
            value: value.into(),
        }
    }

    /// Create a less-than-or-equal condition (column <= value).
    pub fn lte(column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Lte,
            value: value.into(),
        }
    }

    /// Create a LIKE condition.
    pub fn like(column: impl Into<String>, pattern: impl Into<String>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::Like,
            value: SqlValue::Text(pattern.into()),
        }
    }

    /// Create a NOT LIKE condition.
    pub fn not_like(column: impl Into<String>, pattern: impl Into<String>) -> Self {
        Condition::Compare {
            column: column.into(),
            op: Op::NotLike,
            value: SqlValue::Text(pattern.into()),
        }
    }

    /// Create a starts_with condition (LIKE 'pattern%').
    pub fn starts_with(column: impl Into<String>, prefix: impl Into<String>) -> Self {
        Self::like(column, format!("{}%", prefix.into()))
    }

    /// Create an ends_with condition (LIKE '%pattern').
    pub fn ends_with(column: impl Into<String>, suffix: impl Into<String>) -> Self {
        Self::like(column, format!("%{}", suffix.into()))
    }

    /// Create a contains condition (LIKE '%pattern%').
    pub fn contains(column: impl Into<String>, substring: impl Into<String>) -> Self {
        Self::like(column, format!("%{}%", substring.into()))
    }

    /// Create an IN condition.
    pub fn in_<I>(column: impl Into<String>, values: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<SqlValue>,
    {
        Condition::InList {
            column: column.into(),
            values: values.into_iter().map(|v| v.into()).collect(),
            negated: false,
        }
    }

    /// Create a NOT IN condition.
    pub fn not_in<I>(column: impl Into<String>, values: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<SqlValue>,
    {
        Condition::InList {
            column: column.into(),
            values: values.into_iter().map(|v| v.into()).collect(),
            negated: true,
        }
    }

    /// Create a BETWEEN condition.
    pub fn between(
        column: impl Into<String>,
        low: impl Into<SqlValue>,
        high: impl Into<SqlValue>,
    ) -> Self {
        Condition::Between {
            column: column.into(),
            low: low.into(),
            high: high.into(),
        }
    }

    /// Create an IS NULL condition.
    pub fn is_null(column: impl Into<String>) -> Self {
        Condition::Null {
            column: column.into(),
            is_null: true,
        }
    }

    /// Create an IS NOT NULL condition.
    pub fn is_not_null(column: impl Into<String>) -> Self {
        Condition::Null {
            column: column.into(),
            is_null: false,
        }
    }

    /// Create an AND condition.
    pub fn and<I>(conditions: I) -> Self
    where
        I: IntoIterator<Item = Condition>,
    {
        Condition::And(conditions.into_iter().collect())
    }

    /// Create an OR condition.
    pub fn or<I>(conditions: I) -> Self
    where
        I: IntoIterator<Item = Condition>,
    {
        Condition::Or(conditions.into_iter().collect())
    }

    /// Create a NOT condition.
    pub fn not(condition: Condition) -> Self {
        Condition::Not(Box::new(condition))
    }

    /// Create a raw SQL condition.
    pub fn raw(sql: impl Into<String>, params: Vec<SqlValue>) -> Self {
        Condition::Raw {
            sql: sql.into(),
            params,
        }
    }

    /// Build the SQL fragment and parameters for this condition.
    pub fn build(&self, dialect: Dialect) -> (String, Vec<SqlValue>) {
        self.build_with_offset(dialect, 0)
    }

    /// Build the SQL fragment and parameters with a base offset for placeholders.
    pub fn build_with_offset(&self, dialect: Dialect, offset: usize) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let sql = self.build_sql(dialect, &mut params, offset);
        (sql, params)
    }

    fn build_sql(&self, dialect: Dialect, params: &mut Vec<SqlValue>, offset: usize) -> String {
        match self {
            Condition::Compare { column, op, value } => {
                let op_str = match op {
                    Op::Eq => "=",
                    Op::Ne => "!=",
                    Op::Gt => ">",
                    Op::Gte => ">=",
                    Op::Lt => "<",
                    Op::Lte => "<=",
                    Op::Like => "LIKE",
                    Op::NotLike => "NOT LIKE",
                    _ => unreachable!(),
                };
                params.push(value.clone());
                format!(
                    "{} {} {}",
                    column,
                    op_str,
                    dialect.placeholder(offset + params.len())
                )
            }
            Condition::InList {
                column,
                values,
                negated,
            } => {
                let placeholders: Vec<String> = values
                    .iter()
                    .map(|v| {
                        params.push(v.clone());
                        dialect.placeholder(offset + params.len())
                    })
                    .collect();
                let op = if *negated { "NOT IN" } else { "IN" };
                format!("{} {} ({})", column, op, placeholders.join(", "))
            }
            Condition::Between { column, low, high } => {
                params.push(low.clone());
                let p1 = dialect.placeholder(offset + params.len());
                params.push(high.clone());
                let p2 = dialect.placeholder(offset + params.len());
                format!("{} BETWEEN {} AND {}", column, p1, p2)
            }
            Condition::Null { column, is_null } => {
                if *is_null {
                    format!("{} IS NULL", column)
                } else {
                    format!("{} IS NOT NULL", column)
                }
            }
            Condition::And(conditions) => {
                let parts: Vec<String> = conditions
                    .iter()
                    .map(|c| c.build_sql(dialect, params, offset))
                    .collect();
                if parts.len() == 1 {
                    parts[0].clone()
                } else {
                    format!("({})", parts.join(" AND "))
                }
            }
            Condition::Or(conditions) => {
                let parts: Vec<String> = conditions
                    .iter()
                    .map(|c| c.build_sql(dialect, params, offset))
                    .collect();
                if parts.len() == 1 {
                    parts[0].clone()
                } else {
                    format!("({})", parts.join(" OR "))
                }
            }
            Condition::Not(condition) => {
                let inner = condition.build_sql(dialect, params, offset);
                format!("NOT ({})", inner)
            }
            Condition::Raw {
                sql,
                params: raw_params,
            } => {
                params.extend(raw_params.iter().cloned());
                sql.clone()
            }
        }
    }
}

/// SQL dialect for placeholder style.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dialect {
    /// SQLite/libSQL style: ?
    Sqlite,
    /// PostgreSQL style: $1, $2, ...
    Postgres,
}

impl Dialect {
    /// Get the placeholder for the nth parameter (1-indexed).
    pub fn placeholder(&self, n: usize) -> String {
        match self {
            Dialect::Sqlite => "?".to_string(),
            Dialect::Postgres => format!("${}", n),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eq_condition() {
        let cond = Condition::eq("name", "Alice");
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "name = ?");
        assert_eq!(params.len(), 1);
    }

    #[test]
    fn test_comparison_conditions() {
        let cond = Condition::gt("age", 18);
        let (sql, _) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "age > ?");

        let cond = Condition::lte("score", 100);
        let (sql, _) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "score <= ?");
    }

    #[test]
    fn test_like_condition() {
        let cond = Condition::like("name", "%Alice%");
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "name LIKE ?");
        assert_eq!(params[0], SqlValue::Text("%Alice%".to_string()));
    }

    #[test]
    fn test_in_condition() {
        let cond = Condition::in_("status", ["active", "pending"]);
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "status IN (?, ?)");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_between_condition() {
        let cond = Condition::between("age", 18, 65);
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "age BETWEEN ? AND ?");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_null_conditions() {
        let cond = Condition::is_null("deleted_at");
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "deleted_at IS NULL");
        assert!(params.is_empty());

        let cond = Condition::is_not_null("verified_at");
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "verified_at IS NOT NULL");
        assert!(params.is_empty());
    }

    #[test]
    fn test_and_condition() {
        let cond = Condition::and([Condition::eq("status", "active"), Condition::gt("age", 18)]);
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "(status = ? AND age > ?)");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_or_condition() {
        let cond = Condition::or([
            Condition::eq("role", "admin"),
            Condition::eq("role", "superuser"),
        ]);
        let (sql, params) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "(role = ? OR role = ?)");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_not_condition() {
        let cond = Condition::not(Condition::eq("deleted", true));
        let (sql, _) = cond.build(Dialect::Sqlite);
        assert_eq!(sql, "NOT (deleted = ?)");
    }

    #[test]
    fn test_postgres_placeholders() {
        let cond = Condition::and([Condition::eq("name", "Alice"), Condition::gt("age", 18)]);
        let (sql, _) = cond.build(Dialect::Postgres);
        assert_eq!(sql, "(name = $1 AND age > $2)");
    }
}
