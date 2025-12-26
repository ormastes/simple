//! Raw SQL support for escape hatch queries.

use simple_db::{Connection, DbResult, Rows, SqlValue};

/// Raw SQL query wrapper.
///
/// Provides an escape hatch for complex queries that can't be expressed
/// in the query DSL.
#[derive(Debug, Clone)]
pub struct RawSql {
    /// The SQL query string.
    sql: String,
    /// Query parameters.
    params: Vec<SqlValue>,
}

impl RawSql {
    /// Create a new raw SQL query.
    pub fn new(sql: impl Into<String>) -> Self {
        Self {
            sql: sql.into(),
            params: Vec::new(),
        }
    }

    /// Create a raw SQL query with parameters.
    pub fn with_params(sql: impl Into<String>, params: Vec<SqlValue>) -> Self {
        Self {
            sql: sql.into(),
            params,
        }
    }

    /// Add a parameter to the query.
    pub fn bind(mut self, value: impl Into<SqlValue>) -> Self {
        self.params.push(value.into());
        self
    }

    /// Add multiple parameters to the query.
    pub fn bind_all<I>(mut self, values: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<SqlValue>,
    {
        self.params.extend(values.into_iter().map(|v| v.into()));
        self
    }

    /// Get the SQL string.
    pub fn sql(&self) -> &str {
        &self.sql
    }

    /// Get the parameters.
    pub fn params(&self) -> &[SqlValue] {
        &self.params
    }

    /// Execute the query on a connection (for SELECT queries).
    pub fn query<C: Connection + ?Sized>(&self, conn: &C) -> DbResult<Rows> {
        conn.query(&self.sql, &self.params)
    }

    /// Execute the query on a connection (for INSERT/UPDATE/DELETE).
    pub fn execute<C: Connection + ?Sized>(&self, conn: &C) -> DbResult<u64> {
        conn.execute(&self.sql, &self.params)
    }

    /// Build into SQL and parameters tuple.
    pub fn build(self) -> (String, Vec<SqlValue>) {
        (self.sql, self.params)
    }
}

/// Create a raw SQL query.
///
/// # Example
///
/// ```ignore
/// use simple_sqp::raw;
///
/// let query = raw("SELECT * FROM users WHERE status = ?")
///     .bind("active");
/// ```
pub fn raw(sql: impl Into<String>) -> RawSql {
    RawSql::new(sql)
}

/// Create a raw SQL query with parameters.
///
/// # Example
///
/// ```ignore
/// use simple_sqp::raw_with;
///
/// let query = raw_with(
///     "SELECT * FROM users WHERE status = ? AND age > ?",
///     vec!["active".into(), 18.into()]
/// );
/// ```
pub fn raw_with(sql: impl Into<String>, params: Vec<SqlValue>) -> RawSql {
    RawSql::with_params(sql, params)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw_sql_creation() {
        let query = RawSql::new("SELECT * FROM users");
        assert_eq!(query.sql(), "SELECT * FROM users");
        assert!(query.params().is_empty());
    }

    #[test]
    fn test_raw_sql_with_params() {
        let query = RawSql::with_params(
            "SELECT * FROM users WHERE status = ?",
            vec![SqlValue::Text("active".to_string())],
        );
        assert_eq!(query.params().len(), 1);
    }

    #[test]
    fn test_raw_sql_bind() {
        let query = RawSql::new("SELECT * FROM users WHERE name = ? AND age > ?")
            .bind("Alice")
            .bind(18);
        assert_eq!(query.params().len(), 2);
        assert_eq!(query.params()[0], SqlValue::Text("Alice".to_string()));
        assert_eq!(query.params()[1], SqlValue::Integer(18));
    }

    #[test]
    fn test_raw_sql_bind_all() {
        let query = RawSql::new("SELECT * FROM users WHERE id IN (?, ?, ?)")
            .bind_all([1, 2, 3]);
        assert_eq!(query.params().len(), 3);
    }

    #[test]
    fn test_raw_helper() {
        let query = raw("SELECT 1");
        assert_eq!(query.sql(), "SELECT 1");
    }

    #[test]
    fn test_raw_with_helper() {
        let query = raw_with("SELECT * FROM users WHERE id = ?", vec![1.into()]);
        assert_eq!(query.params().len(), 1);
    }

    #[test]
    fn test_build() {
        let (sql, params) = raw("SELECT * FROM users WHERE name = ?")
            .bind("Alice")
            .build();
        assert_eq!(sql, "SELECT * FROM users WHERE name = ?");
        assert_eq!(params.len(), 1);
    }
}
