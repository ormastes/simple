//! Row abstraction for query results.

use crate::error::{DbError, DbResult};
use crate::types::{FromSql, SqlValue};
use std::collections::HashMap;

/// A row from a query result.
pub struct Row {
    /// Column values by index
    values: Vec<SqlValue>,
    /// Column name to index mapping
    column_map: HashMap<String, usize>,
}

impl Row {
    /// Create a new row with values and column names.
    pub fn new(values: Vec<SqlValue>, columns: Vec<String>) -> Self {
        let column_map = columns.iter().enumerate().map(|(i, name)| (name.clone(), i)).collect();
        Self { values, column_map }
    }

    /// Get value by column index.
    pub fn get<T: FromSql>(&self, index: usize) -> DbResult<T> {
        let value = self
            .values
            .get(index)
            .ok_or_else(|| DbError::column_not_found(format!("index {}", index)))?;
        T::from_sql(value)
    }

    /// Get value by column name.
    pub fn get_by_name<T: FromSql>(&self, name: &str) -> DbResult<T> {
        let index = self
            .column_map
            .get(name)
            .ok_or_else(|| DbError::column_not_found(name))?;
        self.get(*index)
    }

    /// Get optional value by index (returns None for NULL).
    pub fn get_opt<T: FromSql>(&self, index: usize) -> DbResult<Option<T>> {
        let value = self
            .values
            .get(index)
            .ok_or_else(|| DbError::column_not_found(format!("index {}", index)))?;
        if value.is_null() {
            Ok(None)
        } else {
            Ok(Some(T::from_sql(value)?))
        }
    }

    /// Get optional value by name.
    pub fn get_opt_by_name<T: FromSql>(&self, name: &str) -> DbResult<Option<T>> {
        let index = self
            .column_map
            .get(name)
            .ok_or_else(|| DbError::column_not_found(name))?;
        self.get_opt(*index)
    }

    /// Get raw SQL value by index.
    pub fn get_value(&self, index: usize) -> Option<&SqlValue> {
        self.values.get(index)
    }

    /// Get raw SQL value by name.
    pub fn get_value_by_name(&self, name: &str) -> Option<&SqlValue> {
        let index = self.column_map.get(name)?;
        self.values.get(*index)
    }

    /// Number of columns.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if row is empty.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Get column names.
    pub fn columns(&self) -> Vec<&str> {
        let mut cols: Vec<_> = self.column_map.iter().collect();
        cols.sort_by_key(|(_, idx)| *idx);
        cols.into_iter().map(|(name, _)| name.as_str()).collect()
    }
}

/// Iterator over rows from a query result.
pub struct Rows {
    /// Inner iterator
    inner: Box<dyn Iterator<Item = DbResult<Row>> + Send>,
    /// Column names
    columns: Vec<String>,
}

impl Rows {
    /// Create a new rows iterator.
    pub fn new(inner: Box<dyn Iterator<Item = DbResult<Row>> + Send>, columns: Vec<String>) -> Self {
        Self { inner, columns }
    }

    /// Create an empty rows iterator.
    pub fn empty() -> Self {
        Self {
            inner: Box::new(std::iter::empty()),
            columns: vec![],
        }
    }

    /// Get column names.
    pub fn columns(&self) -> &[String] {
        &self.columns
    }

    /// Collect all rows into a Vec.
    pub fn collect_all(self) -> DbResult<Vec<Row>> {
        self.inner.collect()
    }
}

impl Iterator for Rows {
    type Item = DbResult<Row>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_row_get_by_index() {
        let row = Row::new(
            vec![SqlValue::Integer(42), SqlValue::Text("hello".to_string())],
            vec!["id".to_string(), "name".to_string()],
        );

        assert_eq!(row.get::<i64>(0).unwrap(), 42);
        assert_eq!(row.get::<String>(1).unwrap(), "hello");
    }

    #[test]
    fn test_row_get_by_name() {
        let row = Row::new(
            vec![SqlValue::Integer(42), SqlValue::Text("hello".to_string())],
            vec!["id".to_string(), "name".to_string()],
        );

        assert_eq!(row.get_by_name::<i64>("id").unwrap(), 42);
        assert_eq!(row.get_by_name::<String>("name").unwrap(), "hello");
    }

    #[test]
    fn test_row_get_opt() {
        let row = Row::new(
            vec![SqlValue::Integer(42), SqlValue::Null],
            vec!["id".to_string(), "optional".to_string()],
        );

        assert_eq!(row.get_opt::<i64>(0).unwrap(), Some(42));
        assert_eq!(row.get_opt::<i64>(1).unwrap(), None);
    }

    #[test]
    fn test_row_columns() {
        let row = Row::new(
            vec![SqlValue::Integer(1), SqlValue::Integer(2)],
            vec!["a".to_string(), "b".to_string()],
        );

        assert_eq!(row.len(), 2);
        assert_eq!(row.columns(), vec!["a", "b"]);
    }
}
