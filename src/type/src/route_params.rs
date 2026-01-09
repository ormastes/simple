//! Route Parameter Extraction
//!
//! This module provides functionality for extracting and parsing parameters from URL routes.
//! Supports path parameters, query parameters, and type conversion.

use std::collections::HashMap;

/// Error types for route parameter extraction
#[derive(Debug, Clone, PartialEq)]
pub enum RouteParamError {
    /// Parameter not found in route
    MissingParameter(String),
    /// Failed to parse parameter to requested type
    ParseError {
        param: String,
        expected_type: String,
    },
    /// Invalid route pattern
    InvalidPattern(String),
    /// Parameter appears multiple times
    DuplicateParameter(String),
}

impl std::fmt::Display for RouteParamError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RouteParamError::MissingParameter(name) => {
                write!(f, "Missing required parameter: {}", name)
            }
            RouteParamError::ParseError {
                param,
                expected_type,
            } => {
                write!(
                    f,
                    "Failed to parse parameter '{}' as {}",
                    param, expected_type
                )
            }
            RouteParamError::InvalidPattern(pattern) => {
                write!(f, "Invalid route pattern: {}", pattern)
            }
            RouteParamError::DuplicateParameter(name) => {
                write!(f, "Duplicate parameter: {}", name)
            }
        }
    }
}

impl std::error::Error for RouteParamError {}

/// Route parameter value
#[derive(Debug, Clone, PartialEq)]
pub enum ParamValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
}

impl ParamValue {
    /// Get as string
    pub fn as_string(&self) -> Result<String, RouteParamError> {
        match self {
            ParamValue::String(s) => Ok(s.clone()),
            _ => Err(RouteParamError::ParseError {
                param: format!("{:?}", self),
                expected_type: "String".to_string(),
            }),
        }
    }

    /// Get as integer
    pub fn as_i64(&self) -> Result<i64, RouteParamError> {
        match self {
            ParamValue::Integer(i) => Ok(*i),
            ParamValue::String(s) => s.parse().map_err(|_| RouteParamError::ParseError {
                param: s.clone(),
                expected_type: "i64".to_string(),
            }),
            _ => Err(RouteParamError::ParseError {
                param: format!("{:?}", self),
                expected_type: "i64".to_string(),
            }),
        }
    }

    /// Get as float
    pub fn as_f64(&self) -> Result<f64, RouteParamError> {
        match self {
            ParamValue::Float(f) => Ok(*f),
            ParamValue::String(s) => s.parse().map_err(|_| RouteParamError::ParseError {
                param: s.clone(),
                expected_type: "f64".to_string(),
            }),
            _ => Err(RouteParamError::ParseError {
                param: format!("{:?}", self),
                expected_type: "f64".to_string(),
            }),
        }
    }

    /// Get as boolean
    pub fn as_bool(&self) -> Result<bool, RouteParamError> {
        match self {
            ParamValue::Boolean(b) => Ok(*b),
            ParamValue::String(s) => match s.to_lowercase().as_str() {
                "true" | "1" | "yes" | "on" => Ok(true),
                "false" | "0" | "no" | "off" => Ok(false),
                _ => Err(RouteParamError::ParseError {
                    param: s.clone(),
                    expected_type: "bool".to_string(),
                }),
            },
            _ => Err(RouteParamError::ParseError {
                param: format!("{:?}", self),
                expected_type: "bool".to_string(),
            }),
        }
    }
}

/// Route parameter extractor
#[derive(Debug, Clone)]
pub struct RouteParams {
    /// Path parameters extracted from URL
    path_params: HashMap<String, ParamValue>,
    /// Query parameters from query string
    query_params: HashMap<String, ParamValue>,
}

impl RouteParams {
    /// Create empty route parameters
    pub fn new() -> Self {
        Self {
            path_params: HashMap::new(),
            query_params: HashMap::new(),
        }
    }

    /// Extract parameters from a route pattern and actual path
    ///
    /// Pattern: "/users/:id/posts/:post_id"
    /// Path: "/users/123/posts/456"
    /// Result: {id: "123", post_id: "456"}
    pub fn from_path(pattern: &str, path: &str) -> Result<Self, RouteParamError> {
        let mut params = Self::new();

        let pattern_segments: Vec<&str> = pattern.split('/').filter(|s| !s.is_empty()).collect();
        let path_segments: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();

        if pattern_segments.len() != path_segments.len() {
            return Err(RouteParamError::InvalidPattern(format!(
                "Pattern '{}' doesn't match path '{}'",
                pattern, path
            )));
        }

        for (pattern_seg, path_seg) in pattern_segments.iter().zip(path_segments.iter()) {
            if pattern_seg.starts_with(':') {
                let param_name = &pattern_seg[1..];

                // Check for duplicate parameters
                if params.path_params.contains_key(param_name) {
                    return Err(RouteParamError::DuplicateParameter(param_name.to_string()));
                }

                params.path_params.insert(
                    param_name.to_string(),
                    ParamValue::String(path_seg.to_string()),
                );
            } else if pattern_seg != path_seg {
                return Err(RouteParamError::InvalidPattern(format!(
                    "Segment '{}' doesn't match '{}'",
                    pattern_seg, path_seg
                )));
            }
        }

        Ok(params)
    }

    /// Parse query string
    ///
    /// Query: "?name=John&age=30&active=true"
    /// Result: {name: "John", age: "30", active: "true"}
    pub fn from_query(query: &str) -> Result<Self, RouteParamError> {
        let mut params = Self::new();

        let query = query.trim_start_matches('?');
        if query.is_empty() {
            return Ok(params);
        }

        for pair in query.split('&') {
            if let Some(pos) = pair.find('=') {
                let key = &pair[..pos];
                let value = &pair[pos + 1..];

                if params.query_params.contains_key(key) {
                    return Err(RouteParamError::DuplicateParameter(key.to_string()));
                }

                params
                    .query_params
                    .insert(key.to_string(), ParamValue::String(value.to_string()));
            }
        }

        Ok(params)
    }

    /// Get path parameter as string
    pub fn get(&self, name: &str) -> Result<String, RouteParamError> {
        self.path_params
            .get(name)
            .ok_or_else(|| RouteParamError::MissingParameter(name.to_string()))
            .and_then(|v| v.as_string())
    }

    /// Get path parameter as i64
    pub fn get_i64(&self, name: &str) -> Result<i64, RouteParamError> {
        self.path_params
            .get(name)
            .ok_or_else(|| RouteParamError::MissingParameter(name.to_string()))
            .and_then(|v| v.as_i64())
    }

    /// Get query parameter as string
    pub fn query(&self, name: &str) -> Result<String, RouteParamError> {
        self.query_params
            .get(name)
            .ok_or_else(|| RouteParamError::MissingParameter(name.to_string()))
            .and_then(|v| v.as_string())
    }

    /// Get query parameter as i64
    pub fn query_i64(&self, name: &str) -> Result<i64, RouteParamError> {
        self.query_params
            .get(name)
            .ok_or_else(|| RouteParamError::MissingParameter(name.to_string()))
            .and_then(|v| v.as_i64())
    }

    /// Get query parameter as bool
    pub fn query_bool(&self, name: &str) -> Result<bool, RouteParamError> {
        self.query_params
            .get(name)
            .ok_or_else(|| RouteParamError::MissingParameter(name.to_string()))
            .and_then(|v| v.as_bool())
    }

    /// Get optional path parameter
    pub fn get_optional(&self, name: &str) -> Option<String> {
        self.path_params.get(name).and_then(|v| v.as_string().ok())
    }

    /// Get optional query parameter
    pub fn query_optional(&self, name: &str) -> Option<String> {
        self.query_params.get(name).and_then(|v| v.as_string().ok())
    }

    /// Check if path parameter exists
    pub fn has(&self, name: &str) -> bool {
        self.path_params.contains_key(name)
    }

    /// Check if query parameter exists
    pub fn has_query(&self, name: &str) -> bool {
        self.query_params.contains_key(name)
    }

    /// Get all path parameter names
    pub fn path_names(&self) -> Vec<String> {
        self.path_params.keys().cloned().collect()
    }

    /// Get all query parameter names
    pub fn query_names(&self) -> Vec<String> {
        self.query_params.keys().cloned().collect()
    }
}

impl Default for RouteParams {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_params_extraction() {
        let params =
            RouteParams::from_path("/users/:id/posts/:post_id", "/users/123/posts/456").unwrap();

        assert_eq!(params.get("id").unwrap(), "123");
        assert_eq!(params.get("post_id").unwrap(), "456");
    }

    #[test]
    fn test_path_params_with_type_conversion() {
        let params = RouteParams::from_path("/users/:id", "/users/123").unwrap();

        assert_eq!(params.get_i64("id").unwrap(), 123);
    }

    #[test]
    fn test_query_params_extraction() {
        let params = RouteParams::from_query("?name=John&age=30&active=true").unwrap();

        assert_eq!(params.query("name").unwrap(), "John");
        assert_eq!(params.query("age").unwrap(), "30");
        assert_eq!(params.query_i64("age").unwrap(), 30);
        assert_eq!(params.query_bool("active").unwrap(), true);
    }

    #[test]
    fn test_missing_parameter() {
        let params = RouteParams::from_path("/users/:id", "/users/123").unwrap();

        assert!(matches!(
            params.get("name"),
            Err(RouteParamError::MissingParameter(_))
        ));
    }

    #[test]
    fn test_invalid_pattern() {
        let result = RouteParams::from_path("/users/:id", "/posts/123");
        assert!(result.is_err());
    }

    #[test]
    fn test_duplicate_parameter() {
        let result = RouteParams::from_path("/users/:id/posts/:id", "/users/123/posts/456");
        assert!(matches!(
            result,
            Err(RouteParamError::DuplicateParameter(_))
        ));
    }

    #[test]
    fn test_optional_parameters() {
        let params = RouteParams::from_path("/users/:id", "/users/123").unwrap();

        assert_eq!(params.get_optional("id"), Some("123".to_string()));
        assert_eq!(params.get_optional("name"), None);
    }

    #[test]
    fn test_has_parameter() {
        let params = RouteParams::from_path("/users/:id", "/users/123").unwrap();

        assert!(params.has("id"));
        assert!(!params.has("name"));
    }

    #[test]
    fn test_parameter_names() {
        let params =
            RouteParams::from_path("/users/:user_id/posts/:post_id", "/users/1/posts/2").unwrap();

        let names = params.path_names();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"user_id".to_string()));
        assert!(names.contains(&"post_id".to_string()));
    }

    #[test]
    fn test_bool_parsing() {
        let params = RouteParams::from_query("?flag1=true&flag2=false&flag3=1&flag4=0").unwrap();

        assert_eq!(params.query_bool("flag1").unwrap(), true);
        assert_eq!(params.query_bool("flag2").unwrap(), false);
        assert_eq!(params.query_bool("flag3").unwrap(), true);
        assert_eq!(params.query_bool("flag4").unwrap(), false);
    }

    #[test]
    fn test_complex_route() {
        let params = RouteParams::from_path(
            "/api/v1/users/:user_id/posts/:post_id/comments/:comment_id",
            "/api/v1/users/100/posts/200/comments/300",
        )
        .unwrap();

        assert_eq!(params.get_i64("user_id").unwrap(), 100);
        assert_eq!(params.get_i64("post_id").unwrap(), 200);
        assert_eq!(params.get_i64("comment_id").unwrap(), 300);
    }

    #[test]
    fn test_empty_query() {
        let params = RouteParams::from_query("").unwrap();
        assert_eq!(params.query_names().len(), 0);
    }
}
