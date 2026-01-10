//! SQL type mapping between Simple types and database types.

use crate::error::{DbError, DbResult};

/// SQL value type for parameter binding and result extraction.
#[derive(Debug, Clone, PartialEq)]
pub enum SqlValue {
    /// NULL value
    Null,
    /// Integer value (i64)
    Integer(i64),
    /// Real/float value (f64)
    Real(f64),
    /// Text/string value
    Text(String),
    /// Binary blob value
    Blob(Vec<u8>),
    /// Boolean value (stored as integer in SQLite)
    Boolean(bool),
}

impl SqlValue {
    /// Check if value is NULL.
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }

    /// Get type name for error messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Null => "null",
            Self::Integer(_) => "integer",
            Self::Real(_) => "real",
            Self::Text(_) => "text",
            Self::Blob(_) => "blob",
            Self::Boolean(_) => "boolean",
        }
    }
}

/// Convert from SQL value to Rust type.
pub trait FromSql: Sized {
    /// Convert from SQL value.
    fn from_sql(value: &SqlValue) -> DbResult<Self>;
}

/// Convert from Rust type to SQL value.
pub trait ToSql {
    /// Convert to SQL value.
    fn to_sql(&self) -> SqlValue;
}

// ============================================================================
// FromSql implementations
// ============================================================================

impl FromSql for i64 {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Integer(i) => Ok(*i),
            SqlValue::Real(f) => Ok(*f as i64),
            other => Err(DbError::type_mismatch("integer", other.type_name())),
        }
    }
}

impl FromSql for i32 {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Integer(i) => Ok(*i as i32),
            SqlValue::Real(f) => Ok(*f as i32),
            other => Err(DbError::type_mismatch("integer", other.type_name())),
        }
    }
}

impl FromSql for f64 {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Real(f) => Ok(*f),
            SqlValue::Integer(i) => Ok(*i as f64),
            other => Err(DbError::type_mismatch("real", other.type_name())),
        }
    }
}

impl FromSql for f32 {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Real(f) => Ok(*f as f32),
            SqlValue::Integer(i) => Ok(*i as f32),
            other => Err(DbError::type_mismatch("real", other.type_name())),
        }
    }
}

impl FromSql for bool {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Boolean(b) => Ok(*b),
            SqlValue::Integer(i) => Ok(*i != 0),
            other => Err(DbError::type_mismatch("boolean", other.type_name())),
        }
    }
}

impl FromSql for String {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Text(s) => Ok(s.clone()),
            SqlValue::Null => Ok(String::new()),
            other => Err(DbError::type_mismatch("text", other.type_name())),
        }
    }
}

impl FromSql for Vec<u8> {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        match value {
            SqlValue::Blob(b) => Ok(b.clone()),
            SqlValue::Text(s) => Ok(s.as_bytes().to_vec()),
            other => Err(DbError::type_mismatch("blob", other.type_name())),
        }
    }
}

impl<T: FromSql> FromSql for Option<T> {
    fn from_sql(value: &SqlValue) -> DbResult<Self> {
        if value.is_null() {
            Ok(None)
        } else {
            Ok(Some(T::from_sql(value)?))
        }
    }
}

// ============================================================================
// ToSql implementations
// ============================================================================

impl ToSql for i64 {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Integer(*self)
    }
}

impl ToSql for i32 {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Integer(*self as i64)
    }
}

impl ToSql for f64 {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Real(*self)
    }
}

impl ToSql for f32 {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Real(*self as f64)
    }
}

impl ToSql for bool {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Boolean(*self)
    }
}

impl ToSql for String {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Text(self.clone())
    }
}

impl ToSql for &str {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Text(self.to_string())
    }
}

impl ToSql for Vec<u8> {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Blob(self.clone())
    }
}

impl ToSql for &[u8] {
    fn to_sql(&self) -> SqlValue {
        SqlValue::Blob(self.to_vec())
    }
}

impl<T: ToSql> ToSql for Option<T> {
    fn to_sql(&self) -> SqlValue {
        match self {
            Some(v) => v.to_sql(),
            None => SqlValue::Null,
        }
    }
}

impl ToSql for SqlValue {
    fn to_sql(&self) -> SqlValue {
        self.clone()
    }
}

// ============================================================================
// From implementations for ergonomic parameter building
// ============================================================================

impl From<i64> for SqlValue {
    fn from(v: i64) -> Self {
        SqlValue::Integer(v)
    }
}

impl From<i32> for SqlValue {
    fn from(v: i32) -> Self {
        SqlValue::Integer(v as i64)
    }
}

impl From<f64> for SqlValue {
    fn from(v: f64) -> Self {
        SqlValue::Real(v)
    }
}

impl From<f32> for SqlValue {
    fn from(v: f32) -> Self {
        SqlValue::Real(v as f64)
    }
}

impl From<bool> for SqlValue {
    fn from(v: bool) -> Self {
        SqlValue::Boolean(v)
    }
}

impl From<String> for SqlValue {
    fn from(v: String) -> Self {
        SqlValue::Text(v)
    }
}

impl From<&str> for SqlValue {
    fn from(v: &str) -> Self {
        SqlValue::Text(v.to_string())
    }
}

impl From<Vec<u8>> for SqlValue {
    fn from(v: Vec<u8>) -> Self {
        SqlValue::Blob(v)
    }
}

impl<T: Into<SqlValue>> From<Option<T>> for SqlValue {
    fn from(v: Option<T>) -> Self {
        match v {
            Some(v) => v.into(),
            None => SqlValue::Null,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_sql_integer() {
        let v = SqlValue::Integer(42);
        assert_eq!(i64::from_sql(&v).unwrap(), 42);
        assert_eq!(i32::from_sql(&v).unwrap(), 42);
        assert_eq!(f64::from_sql(&v).unwrap(), 42.0);
    }

    #[test]
    fn test_from_sql_real() {
        let v = SqlValue::Real(3.15);
        assert_eq!(f64::from_sql(&v).unwrap(), 3.15);
        assert_eq!(f32::from_sql(&v).unwrap(), 3.15f32);
        assert_eq!(i64::from_sql(&v).unwrap(), 3);
    }

    #[test]
    fn test_from_sql_text() {
        let v = SqlValue::Text("hello".to_string());
        assert_eq!(String::from_sql(&v).unwrap(), "hello");
    }

    #[test]
    fn test_from_sql_bool() {
        let v = SqlValue::Boolean(true);
        assert!(bool::from_sql(&v).unwrap());

        let v = SqlValue::Integer(1);
        assert!(bool::from_sql(&v).unwrap());

        let v = SqlValue::Integer(0);
        assert!(!bool::from_sql(&v).unwrap());
    }

    #[test]
    fn test_from_sql_option() {
        let v = SqlValue::Null;
        assert_eq!(Option::<i64>::from_sql(&v).unwrap(), None);

        let v = SqlValue::Integer(42);
        assert_eq!(Option::<i64>::from_sql(&v).unwrap(), Some(42));
    }

    #[test]
    fn test_to_sql() {
        assert_eq!(42i64.to_sql(), SqlValue::Integer(42));
        assert_eq!(3.15f64.to_sql(), SqlValue::Real(3.15));
        assert_eq!(true.to_sql(), SqlValue::Boolean(true));
        assert_eq!("hello".to_sql(), SqlValue::Text("hello".to_string()));
        assert_eq!(None::<i64>.to_sql(), SqlValue::Null);
    }
}
