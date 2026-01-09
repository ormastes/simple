//! SDN runtime value types.

use indexmap::IndexMap;
use std::fmt;

/// SDN value representing any parsed SDN data.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum SdnValue {
    /// Null value (null or nil)
    #[default]
    Null,
    /// Boolean value
    Bool(bool),
    /// 64-bit signed integer
    Int(i64),
    /// 64-bit floating point number
    Float(f64),
    /// String value (quoted or bare)
    String(String),
    /// Array of values
    Array(Vec<SdnValue>),
    /// Dictionary (ordered key-value pairs)
    Dict(IndexMap<String, SdnValue>),
    /// Table with uniform records
    Table {
        /// Named fields (for named tables) or None for typed tables
        fields: Option<Vec<String>>,
        /// Type names (for typed tables) or None for named tables
        types: Option<Vec<String>>,
        /// Table rows
        rows: Vec<Vec<SdnValue>>,
    },
}

impl SdnValue {
    /// Create a new null value.
    pub fn null() -> Self {
        SdnValue::Null
    }

    /// Create a new boolean value.
    pub fn bool(b: bool) -> Self {
        SdnValue::Bool(b)
    }

    /// Create a new integer value.
    pub fn int(i: i64) -> Self {
        SdnValue::Int(i)
    }

    /// Create a new float value.
    pub fn float(f: f64) -> Self {
        SdnValue::Float(f)
    }

    /// Create a new string value.
    pub fn string(s: impl Into<String>) -> Self {
        SdnValue::String(s.into())
    }

    /// Create a new array value.
    pub fn array(values: Vec<SdnValue>) -> Self {
        SdnValue::Array(values)
    }

    /// Create a new empty dictionary.
    pub fn dict() -> Self {
        SdnValue::Dict(IndexMap::new())
    }

    /// Create a new named table.
    pub fn named_table(fields: Vec<String>, rows: Vec<Vec<SdnValue>>) -> Self {
        SdnValue::Table {
            fields: Some(fields),
            types: None,
            rows,
        }
    }

    /// Create a new typed table.
    pub fn typed_table(types: Vec<String>, rows: Vec<Vec<SdnValue>>) -> Self {
        SdnValue::Table {
            fields: None,
            types: Some(types),
            rows,
        }
    }

    /// Check if value is null.
    pub fn is_null(&self) -> bool {
        matches!(self, SdnValue::Null)
    }

    /// Check if value is a boolean.
    pub fn is_bool(&self) -> bool {
        matches!(self, SdnValue::Bool(_))
    }

    /// Check if value is an integer.
    pub fn is_int(&self) -> bool {
        matches!(self, SdnValue::Int(_))
    }

    /// Check if value is a float.
    pub fn is_float(&self) -> bool {
        matches!(self, SdnValue::Float(_))
    }

    /// Check if value is a number (int or float).
    pub fn is_number(&self) -> bool {
        matches!(self, SdnValue::Int(_) | SdnValue::Float(_))
    }

    /// Check if value is a string.
    pub fn is_string(&self) -> bool {
        matches!(self, SdnValue::String(_))
    }

    /// Check if value is an array.
    pub fn is_array(&self) -> bool {
        matches!(self, SdnValue::Array(_))
    }

    /// Check if value is a dict.
    pub fn is_dict(&self) -> bool {
        matches!(self, SdnValue::Dict(_))
    }

    /// Check if value is a table.
    pub fn is_table(&self) -> bool {
        matches!(self, SdnValue::Table { .. })
    }

    /// Get value as bool.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            SdnValue::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Get value as i64.
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            SdnValue::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// Get value as f64.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            SdnValue::Float(f) => Some(*f),
            SdnValue::Int(i) => Some(*i as f64),
            _ => None,
        }
    }

    /// Get value as string slice.
    pub fn as_str(&self) -> Option<&str> {
        match self {
            SdnValue::String(s) => Some(s),
            _ => None,
        }
    }

    /// Get value as array slice.
    pub fn as_array(&self) -> Option<&[SdnValue]> {
        match self {
            SdnValue::Array(arr) => Some(arr),
            _ => None,
        }
    }

    /// Get mutable array reference.
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<SdnValue>> {
        match self {
            SdnValue::Array(arr) => Some(arr),
            _ => None,
        }
    }

    /// Get value as dict reference.
    pub fn as_dict(&self) -> Option<&IndexMap<String, SdnValue>> {
        match self {
            SdnValue::Dict(dict) => Some(dict),
            _ => None,
        }
    }

    /// Get mutable dict reference.
    pub fn as_dict_mut(&mut self) -> Option<&mut IndexMap<String, SdnValue>> {
        match self {
            SdnValue::Dict(dict) => Some(dict),
            _ => None,
        }
    }

    /// Get value at key (for dicts) or index (for arrays).
    pub fn get(&self, key: &str) -> Option<&SdnValue> {
        match self {
            SdnValue::Dict(dict) => dict.get(key),
            SdnValue::Array(arr) => {
                let idx: usize = key.parse().ok()?;
                arr.get(idx)
            }
            SdnValue::Table { fields, rows, .. } => {
                // For tables with named fields, treat first component as row index
                // e.g., "0" returns the first row as an array
                if let Ok(idx) = key.parse::<usize>() {
                    if idx < rows.len() {
                        // Return as a temporary - this is a limitation
                        return None;
                    }
                }
                // For field access on table, not directly supported
                _ = fields;
                None
            }
            _ => None,
        }
    }

    /// Get mutable value at key.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut SdnValue> {
        match self {
            SdnValue::Dict(dict) => dict.get_mut(key),
            SdnValue::Array(arr) => {
                let idx: usize = key.parse().ok()?;
                arr.get_mut(idx)
            }
            _ => None,
        }
    }

    /// Get value at a dotted path (e.g., "server.port").
    pub fn get_path(&self, path: &str) -> Option<&SdnValue> {
        let mut current = self;
        for key in path.split('.') {
            current = current.get(key)?;
        }
        Some(current)
    }

    /// Get mutable value at a dotted path.
    pub fn get_path_mut(&mut self, path: &str) -> Option<&mut SdnValue> {
        let keys: Vec<&str> = path.split('.').collect();
        let mut current = self;
        for key in keys {
            current = current.get_mut(key)?;
        }
        Some(current)
    }

    /// Insert a value into a dict.
    pub fn insert(&mut self, key: impl Into<String>, value: SdnValue) -> Option<SdnValue> {
        match self {
            SdnValue::Dict(dict) => dict.insert(key.into(), value),
            _ => None,
        }
    }

    /// Push a value to an array.
    pub fn push(&mut self, value: SdnValue) -> bool {
        match self {
            SdnValue::Array(arr) => {
                arr.push(value);
                true
            }
            _ => false,
        }
    }

    /// Get type name for this value.
    pub fn type_name(&self) -> &'static str {
        match self {
            SdnValue::Null => "null",
            SdnValue::Bool(_) => "bool",
            SdnValue::Int(_) => "int",
            SdnValue::Float(_) => "float",
            SdnValue::String(_) => "string",
            SdnValue::Array(_) => "array",
            SdnValue::Dict(_) => "dict",
            SdnValue::Table { .. } => "table",
        }
    }
}

impl fmt::Display for SdnValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SdnValue::Null => write!(f, "null"),
            SdnValue::Bool(b) => write!(f, "{}", b),
            SdnValue::Int(i) => write!(f, "{}", i),
            SdnValue::Float(fl) => write!(f, "{}", fl),
            SdnValue::String(s) => {
                // Quote if contains special chars or spaces
                if s.contains(|c: char| c.is_whitespace() || c == ',' || c == ':') {
                    write!(f, "\"{}\"", s.replace('\"', "\\\""))
                } else {
                    write!(f, "{}", s)
                }
            }
            SdnValue::Array(arr) => {
                write!(f, "[")?;
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            SdnValue::Dict(dict) => {
                write!(f, "{{")?;
                for (i, (k, v)) in dict.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            SdnValue::Table { fields, rows, .. } => {
                if let Some(fields) = fields {
                    write!(f, "|{}|", fields.join(", "))?;
                }
                for row in rows {
                    write!(f, "\n    ")?;
                    for (i, v) in row.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", v)?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl From<bool> for SdnValue {
    fn from(b: bool) -> Self {
        SdnValue::Bool(b)
    }
}

impl From<i64> for SdnValue {
    fn from(i: i64) -> Self {
        SdnValue::Int(i)
    }
}

impl From<i32> for SdnValue {
    fn from(i: i32) -> Self {
        SdnValue::Int(i as i64)
    }
}

impl From<f64> for SdnValue {
    fn from(f: f64) -> Self {
        SdnValue::Float(f)
    }
}

impl From<&str> for SdnValue {
    fn from(s: &str) -> Self {
        SdnValue::String(s.to_string())
    }
}

impl From<String> for SdnValue {
    fn from(s: String) -> Self {
        SdnValue::String(s)
    }
}

impl<T: Into<SdnValue>> From<Vec<T>> for SdnValue {
    fn from(v: Vec<T>) -> Self {
        SdnValue::Array(v.into_iter().map(Into::into).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_types() {
        assert!(SdnValue::Null.is_null());
        assert!(SdnValue::Bool(true).is_bool());
        assert!(SdnValue::Int(42).is_int());
        assert!(SdnValue::Float(3.14).is_float());
        assert!(SdnValue::String("hello".into()).is_string());
        assert!(SdnValue::Array(vec![]).is_array());
        assert!(SdnValue::Dict(IndexMap::new()).is_dict());
    }

    #[test]
    fn test_as_methods() {
        assert_eq!(SdnValue::Bool(true).as_bool(), Some(true));
        assert_eq!(SdnValue::Int(42).as_i64(), Some(42));
        assert_eq!(SdnValue::Float(3.14).as_f64(), Some(3.14));
        assert_eq!(SdnValue::Int(42).as_f64(), Some(42.0));
        assert_eq!(SdnValue::String("hello".into()).as_str(), Some("hello"));
    }

    #[test]
    fn test_dict_operations() {
        let mut dict = SdnValue::dict();
        dict.insert("name", SdnValue::string("Alice"));
        dict.insert("age", SdnValue::int(30));

        assert_eq!(dict.get("name").and_then(|v| v.as_str()), Some("Alice"));
        assert_eq!(dict.get("age").and_then(|v| v.as_i64()), Some(30));
    }

    #[test]
    fn test_path_access() {
        let mut root = SdnValue::dict();
        let mut server = SdnValue::dict();
        server.insert("port", SdnValue::int(8080));
        root.insert("server", server);

        assert_eq!(
            root.get_path("server.port").and_then(|v| v.as_i64()),
            Some(8080)
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", SdnValue::Null), "null");
        assert_eq!(format!("{}", SdnValue::Bool(true)), "true");
        assert_eq!(format!("{}", SdnValue::Int(42)), "42");
        assert_eq!(format!("{}", SdnValue::String("hello".into())), "hello");
        assert_eq!(
            format!("{}", SdnValue::String("hello world".into())),
            "\"hello world\""
        );
    }
}
