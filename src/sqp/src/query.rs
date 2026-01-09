//! Query builder for constructing SQL queries.

use crate::condition::{Condition, Dialect};
use simple_db::SqlValue;

/// Sort order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Order {
    /// Ascending order.
    Asc,
    /// Descending order.
    Desc,
}

impl Order {
    fn as_str(&self) -> &'static str {
        match self {
            Order::Asc => "ASC",
            Order::Desc => "DESC",
        }
    }
}

/// Join type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinType {
    /// Inner join.
    Inner,
    /// Left outer join.
    Left,
    /// Right outer join.
    Right,
    /// Full outer join.
    Full,
}

impl JoinType {
    fn as_str(&self) -> &'static str {
        match self {
            JoinType::Inner => "INNER JOIN",
            JoinType::Left => "LEFT JOIN",
            JoinType::Right => "RIGHT JOIN",
            JoinType::Full => "FULL JOIN",
        }
    }
}

/// A join clause.
#[derive(Debug, Clone)]
struct JoinClause {
    join_type: JoinType,
    table: String,
    on: String,
}

/// A query builder.
#[derive(Debug, Clone)]
pub struct Query {
    /// Table name.
    table: String,
    /// Columns to select.
    select_columns: Vec<String>,
    /// Whether to select distinct rows.
    distinct: bool,
    /// WHERE conditions.
    conditions: Vec<Condition>,
    /// JOIN clauses.
    joins: Vec<JoinClause>,
    /// ORDER BY clauses.
    order_by: Vec<(String, Order)>,
    /// GROUP BY columns.
    group_by: Vec<String>,
    /// HAVING conditions.
    having: Vec<Condition>,
    /// LIMIT.
    limit: Option<u64>,
    /// OFFSET.
    offset: Option<u64>,
    /// SQL dialect.
    dialect: Dialect,
}

impl Query {
    /// Create a new query for a table.
    pub fn table(table: impl Into<String>) -> Self {
        Self {
            table: table.into(),
            select_columns: vec!["*".to_string()],
            distinct: false,
            conditions: Vec::new(),
            joins: Vec::new(),
            order_by: Vec::new(),
            group_by: Vec::new(),
            having: Vec::new(),
            limit: None,
            offset: None,
            dialect: Dialect::Sqlite,
        }
    }

    /// Set the SQL dialect.
    pub fn dialect(mut self, dialect: Dialect) -> Self {
        self.dialect = dialect;
        self
    }

    /// Select specific columns.
    pub fn select<I, S>(mut self, columns: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.select_columns = columns.into_iter().map(|s| s.into()).collect();
        self
    }

    /// Add a column to select.
    pub fn add_select(mut self, column: impl Into<String>) -> Self {
        let col = column.into();
        if self.select_columns == vec!["*".to_string()] {
            self.select_columns = vec![col];
        } else {
            self.select_columns.push(col);
        }
        self
    }

    /// Select distinct rows.
    pub fn distinct(mut self) -> Self {
        self.distinct = true;
        self
    }

    /// Add a WHERE condition.
    pub fn where_(mut self, condition: Condition) -> Self {
        self.conditions.push(condition);
        self
    }

    /// Add an equality WHERE condition.
    pub fn where_eq(self, column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        self.where_(Condition::eq(column, value))
    }

    /// Add a raw WHERE condition.
    pub fn where_raw(self, sql: impl Into<String>, params: Vec<SqlValue>) -> Self {
        self.where_(Condition::raw(sql, params))
    }

    /// Add a JOIN clause.
    pub fn join(mut self, table: impl Into<String>, on: impl Into<String>) -> Self {
        self.joins.push(JoinClause {
            join_type: JoinType::Inner,
            table: table.into(),
            on: on.into(),
        });
        self
    }

    /// Add a LEFT JOIN clause.
    pub fn left_join(mut self, table: impl Into<String>, on: impl Into<String>) -> Self {
        self.joins.push(JoinClause {
            join_type: JoinType::Left,
            table: table.into(),
            on: on.into(),
        });
        self
    }

    /// Add a RIGHT JOIN clause.
    pub fn right_join(mut self, table: impl Into<String>, on: impl Into<String>) -> Self {
        self.joins.push(JoinClause {
            join_type: JoinType::Right,
            table: table.into(),
            on: on.into(),
        });
        self
    }

    /// Add a FULL JOIN clause.
    pub fn full_join(mut self, table: impl Into<String>, on: impl Into<String>) -> Self {
        self.joins.push(JoinClause {
            join_type: JoinType::Full,
            table: table.into(),
            on: on.into(),
        });
        self
    }

    /// Add an ORDER BY clause.
    pub fn order_by(mut self, column: impl Into<String>, order: Order) -> Self {
        self.order_by.push((column.into(), order));
        self
    }

    /// Add an ascending ORDER BY clause.
    pub fn order_asc(self, column: impl Into<String>) -> Self {
        self.order_by(column, Order::Asc)
    }

    /// Add a descending ORDER BY clause.
    pub fn order_desc(self, column: impl Into<String>) -> Self {
        self.order_by(column, Order::Desc)
    }

    /// Add a GROUP BY clause.
    pub fn group_by<I, S>(mut self, columns: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.group_by = columns.into_iter().map(|s| s.into()).collect();
        self
    }

    /// Add a HAVING condition.
    pub fn having(mut self, condition: Condition) -> Self {
        self.having.push(condition);
        self
    }

    /// Set the LIMIT.
    pub fn limit(mut self, limit: u64) -> Self {
        self.limit = Some(limit);
        self
    }

    /// Set the OFFSET.
    pub fn offset(mut self, offset: u64) -> Self {
        self.offset = Some(offset);
        self
    }

    /// Set page-based pagination.
    pub fn page(self, page: u64, per_page: u64) -> Self {
        let offset = (page.saturating_sub(1)) * per_page;
        self.limit(per_page).offset(offset)
    }

    /// Build the SQL query and parameters.
    pub fn build(&self) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let mut sql = String::new();

        // SELECT clause
        sql.push_str("SELECT ");
        if self.distinct {
            sql.push_str("DISTINCT ");
        }
        sql.push_str(&self.select_columns.join(", "));

        // FROM clause
        sql.push_str(" FROM ");
        sql.push_str(&self.table);

        // JOIN clauses
        for join in &self.joins {
            sql.push(' ');
            sql.push_str(join.join_type.as_str());
            sql.push(' ');
            sql.push_str(&join.table);
            sql.push_str(" ON ");
            sql.push_str(&join.on);
        }

        // WHERE clause
        if !self.conditions.is_empty() {
            sql.push_str(" WHERE ");
            let condition_strs: Vec<String> = self
                .conditions
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&condition_strs.join(" AND "));
        }

        // GROUP BY clause
        if !self.group_by.is_empty() {
            sql.push_str(" GROUP BY ");
            sql.push_str(&self.group_by.join(", "));
        }

        // HAVING clause
        if !self.having.is_empty() {
            sql.push_str(" HAVING ");
            let having_strs: Vec<String> = self
                .having
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&having_strs.join(" AND "));
        }

        // ORDER BY clause
        if !self.order_by.is_empty() {
            sql.push_str(" ORDER BY ");
            let order_strs: Vec<String> = self
                .order_by
                .iter()
                .map(|(col, ord)| format!("{} {}", col, ord.as_str()))
                .collect();
            sql.push_str(&order_strs.join(", "));
        }

        // LIMIT clause
        if let Some(limit) = self.limit {
            sql.push_str(" LIMIT ");
            sql.push_str(&limit.to_string());
        }

        // OFFSET clause
        if let Some(offset) = self.offset {
            sql.push_str(" OFFSET ");
            sql.push_str(&offset.to_string());
        }

        (sql, params)
    }

    /// Build a COUNT(*) query.
    pub fn build_count(&self) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let mut sql = String::from("SELECT COUNT(*) FROM ");
        sql.push_str(&self.table);

        // JOIN clauses
        for join in &self.joins {
            sql.push(' ');
            sql.push_str(join.join_type.as_str());
            sql.push(' ');
            sql.push_str(&join.table);
            sql.push_str(" ON ");
            sql.push_str(&join.on);
        }

        // WHERE clause
        if !self.conditions.is_empty() {
            sql.push_str(" WHERE ");
            let condition_strs: Vec<String> = self
                .conditions
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&condition_strs.join(" AND "));
        }

        // GROUP BY clause (for counting groups)
        if !self.group_by.is_empty() {
            sql.push_str(" GROUP BY ");
            sql.push_str(&self.group_by.join(", "));
        }

        // HAVING clause
        if !self.having.is_empty() {
            sql.push_str(" HAVING ");
            let having_strs: Vec<String> = self
                .having
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&having_strs.join(" AND "));
        }

        (sql, params)
    }
}

/// INSERT query builder.
#[derive(Debug, Clone)]
pub struct Insert {
    table: String,
    columns: Vec<String>,
    values: Vec<Vec<SqlValue>>,
    dialect: Dialect,
}

impl Insert {
    /// Create a new INSERT query.
    pub fn into(table: impl Into<String>) -> Self {
        Self {
            table: table.into(),
            columns: Vec::new(),
            values: Vec::new(),
            dialect: Dialect::Sqlite,
        }
    }

    /// Set the SQL dialect.
    pub fn dialect(mut self, dialect: Dialect) -> Self {
        self.dialect = dialect;
        self
    }

    /// Set the columns to insert.
    pub fn columns<I, S>(mut self, columns: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.columns = columns.into_iter().map(|s| s.into()).collect();
        self
    }

    /// Add a row of values.
    pub fn values<I>(mut self, values: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<SqlValue>,
    {
        self.values
            .push(values.into_iter().map(|v| v.into()).collect());
        self
    }

    /// Build the SQL query and parameters.
    pub fn build(&self) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let mut sql = String::from("INSERT INTO ");
        sql.push_str(&self.table);

        if !self.columns.is_empty() {
            sql.push_str(" (");
            sql.push_str(&self.columns.join(", "));
            sql.push(')');
        }

        sql.push_str(" VALUES ");

        let row_strs: Vec<String> = self
            .values
            .iter()
            .map(|row| {
                let placeholders: Vec<String> = row
                    .iter()
                    .map(|v| {
                        params.push(v.clone());
                        self.dialect.placeholder(params.len())
                    })
                    .collect();
                format!("({})", placeholders.join(", "))
            })
            .collect();

        sql.push_str(&row_strs.join(", "));

        (sql, params)
    }
}

/// UPDATE query builder.
#[derive(Debug, Clone)]
pub struct Update {
    table: String,
    sets: Vec<(String, SqlValue)>,
    conditions: Vec<Condition>,
    dialect: Dialect,
}

impl Update {
    /// Create a new UPDATE query.
    pub fn table(table: impl Into<String>) -> Self {
        Self {
            table: table.into(),
            sets: Vec::new(),
            conditions: Vec::new(),
            dialect: Dialect::Sqlite,
        }
    }

    /// Set the SQL dialect.
    pub fn dialect(mut self, dialect: Dialect) -> Self {
        self.dialect = dialect;
        self
    }

    /// Set a column value.
    pub fn set(mut self, column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        self.sets.push((column.into(), value.into()));
        self
    }

    /// Add a WHERE condition.
    pub fn where_(mut self, condition: Condition) -> Self {
        self.conditions.push(condition);
        self
    }

    /// Add an equality WHERE condition.
    pub fn where_eq(self, column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        self.where_(Condition::eq(column, value))
    }

    /// Build the SQL query and parameters.
    pub fn build(&self) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let mut sql = String::from("UPDATE ");
        sql.push_str(&self.table);
        sql.push_str(" SET ");

        let set_strs: Vec<String> = self
            .sets
            .iter()
            .map(|(col, val)| {
                params.push(val.clone());
                format!("{} = {}", col, self.dialect.placeholder(params.len()))
            })
            .collect();

        sql.push_str(&set_strs.join(", "));

        if !self.conditions.is_empty() {
            sql.push_str(" WHERE ");
            let condition_strs: Vec<String> = self
                .conditions
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&condition_strs.join(" AND "));
        }

        (sql, params)
    }
}

/// DELETE query builder.
#[derive(Debug, Clone)]
pub struct Delete {
    table: String,
    conditions: Vec<Condition>,
    dialect: Dialect,
}

impl Delete {
    /// Create a new DELETE query.
    pub fn from(table: impl Into<String>) -> Self {
        Self {
            table: table.into(),
            conditions: Vec::new(),
            dialect: Dialect::Sqlite,
        }
    }

    /// Set the SQL dialect.
    pub fn dialect(mut self, dialect: Dialect) -> Self {
        self.dialect = dialect;
        self
    }

    /// Add a WHERE condition.
    pub fn where_(mut self, condition: Condition) -> Self {
        self.conditions.push(condition);
        self
    }

    /// Add an equality WHERE condition.
    pub fn where_eq(self, column: impl Into<String>, value: impl Into<SqlValue>) -> Self {
        self.where_(Condition::eq(column, value))
    }

    /// Build the SQL query and parameters.
    pub fn build(&self) -> (String, Vec<SqlValue>) {
        let mut params = Vec::new();
        let mut sql = String::from("DELETE FROM ");
        sql.push_str(&self.table);

        if !self.conditions.is_empty() {
            sql.push_str(" WHERE ");
            let condition_strs: Vec<String> = self
                .conditions
                .iter()
                .map(|c| {
                    let (cond_sql, cond_params) = c.build_with_offset(self.dialect, params.len());
                    params.extend(cond_params);
                    cond_sql
                })
                .collect();
            sql.push_str(&condition_strs.join(" AND "));
        }

        (sql, params)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_select() {
        let query = Query::table("users");
        let (sql, params) = query.build();
        assert_eq!(sql, "SELECT * FROM users");
        assert!(params.is_empty());
    }

    #[test]
    fn test_select_columns() {
        let query = Query::table("users").select(["id", "name", "email"]);
        let (sql, _) = query.build();
        assert_eq!(sql, "SELECT id, name, email FROM users");
    }

    #[test]
    fn test_select_with_where() {
        let query = Query::table("users")
            .where_(Condition::eq("status", "active"))
            .where_(Condition::gt("age", 18));
        let (sql, params) = query.build();
        assert_eq!(sql, "SELECT * FROM users WHERE status = ? AND age > ?");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_order_and_limit() {
        let query = Query::table("users")
            .order_asc("name")
            .order_desc("created_at")
            .limit(10)
            .offset(20);
        let (sql, _) = query.build();
        assert_eq!(
            sql,
            "SELECT * FROM users ORDER BY name ASC, created_at DESC LIMIT 10 OFFSET 20"
        );
    }

    #[test]
    fn test_pagination() {
        let query = Query::table("users").page(3, 10);
        let (sql, _) = query.build();
        assert_eq!(sql, "SELECT * FROM users LIMIT 10 OFFSET 20");
    }

    #[test]
    fn test_join() {
        let query = Query::table("users")
            .select(["users.id", "users.name", "posts.title"])
            .join("posts", "posts.user_id = users.id");
        let (sql, _) = query.build();
        assert_eq!(
            sql,
            "SELECT users.id, users.name, posts.title FROM users INNER JOIN posts ON posts.user_id = users.id"
        );
    }

    #[test]
    fn test_left_join() {
        let query = Query::table("users").left_join("posts", "posts.user_id = users.id");
        let (sql, _) = query.build();
        assert!(sql.contains("LEFT JOIN"));
    }

    #[test]
    fn test_group_by() {
        let query = Query::table("posts")
            .select(["user_id", "COUNT(*) as post_count"])
            .group_by(["user_id"]);
        let (sql, _) = query.build();
        assert_eq!(
            sql,
            "SELECT user_id, COUNT(*) as post_count FROM posts GROUP BY user_id"
        );
    }

    #[test]
    fn test_count_query() {
        let query = Query::table("users").where_(Condition::eq("active", true));
        let (sql, params) = query.build_count();
        assert_eq!(sql, "SELECT COUNT(*) FROM users WHERE active = ?");
        assert_eq!(params.len(), 1);
    }

    #[test]
    fn test_insert() {
        let insert = Insert::into("users")
            .columns(["name", "email"])
            .values(["Alice", "alice@example.com"]);
        let (sql, params) = insert.build();
        assert_eq!(sql, "INSERT INTO users (name, email) VALUES (?, ?)");
        assert_eq!(params.len(), 2);
    }

    #[test]
    fn test_insert_multiple() {
        let insert = Insert::into("users")
            .columns(["name", "email"])
            .values(["Alice", "alice@example.com"])
            .values(["Bob", "bob@example.com"]);
        let (sql, params) = insert.build();
        assert_eq!(sql, "INSERT INTO users (name, email) VALUES (?, ?), (?, ?)");
        assert_eq!(params.len(), 4);
    }

    #[test]
    fn test_update() {
        let update = Update::table("users")
            .set("name", "Alice Smith")
            .set("updated_at", "2024-01-01")
            .where_eq("id", 1);
        let (sql, params) = update.build();
        assert_eq!(
            sql,
            "UPDATE users SET name = ?, updated_at = ? WHERE id = ?"
        );
        assert_eq!(params.len(), 3);
    }

    #[test]
    fn test_delete() {
        let delete = Delete::from("users").where_eq("id", 1);
        let (sql, params) = delete.build();
        assert_eq!(sql, "DELETE FROM users WHERE id = ?");
        assert_eq!(params.len(), 1);
    }

    #[test]
    fn test_postgres_dialect() {
        let query = Query::table("users")
            .dialect(Dialect::Postgres)
            .where_(Condition::eq("name", "Alice"))
            .where_(Condition::gt("age", 18));
        let (sql, _) = query.build();
        assert_eq!(sql, "SELECT * FROM users WHERE name = $1 AND age > $2");
    }
}
