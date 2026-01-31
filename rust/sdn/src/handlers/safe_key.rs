//! Handler that rejects dangerous keys
//!
//! This handler validates dictionary keys and table field names to prevent
//! security issues like prototype pollution and path traversal.

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::handlers::ValueBuilder;
use crate::value::SdnValue;

/// Handler that validates keys for security
///
/// This handler rejects:
/// - Prototype pollution keys (__proto__, constructor, prototype)
/// - Path traversal sequences (.., /, \)
/// - Control characters in keys
pub struct SafeKeyHandler {
    inner: ValueBuilder,
}

impl SafeKeyHandler {
    /// Create a new SafeKeyHandler
    pub fn new() -> Self {
        Self {
            inner: ValueBuilder::new(),
        }
    }

    fn validate_key(&self, key: &str, span: Span) -> Result<()> {
        // Reject prototype pollution keys
        if matches!(key, "__proto__" | "constructor" | "prototype") {
            return Err(SdnError::SecurityError {
                message: format!("Unsafe key rejected: {}", key),
                span: Some(span),
            });
        }

        // Reject path traversal
        if key.contains("..") || key.starts_with('/') || key.starts_with('\\') {
            return Err(SdnError::SecurityError {
                message: format!("Path traversal rejected: {}", key),
                span: Some(span),
            });
        }

        // Reject control characters
        if key.chars().any(|c| c.is_control()) {
            return Err(SdnError::SecurityError {
                message: format!("Control characters not allowed in keys: {:?}", key),
                span: Some(span),
            });
        }

        Ok(())
    }
}

impl DataHandler for SafeKeyHandler {
    fn on_null(&mut self, span: Span) -> Result<()> {
        self.inner.on_null(span)
    }

    fn on_bool(&mut self, value: bool, span: Span) -> Result<()> {
        self.inner.on_bool(value, span)
    }

    fn on_int(&mut self, value: i64, span: Span) -> Result<()> {
        self.inner.on_int(value, span)
    }

    fn on_float(&mut self, value: f64, span: Span) -> Result<()> {
        self.inner.on_float(value, span)
    }

    fn on_string(&mut self, value: &str, span: Span) -> Result<()> {
        self.inner.on_string(value, span)
    }
}

impl OpHandler for SafeKeyHandler {
    fn dict_key(&mut self, key: &str, span: Span) -> Result<()> {
        self.validate_key(key, span)?;
        self.inner.dict_key(key, span)
    }

    fn begin_dict(&mut self, span: Span) -> Result<()> {
        self.inner.begin_dict(span)
    }

    fn end_dict(&mut self) -> Result<()> {
        self.inner.end_dict()
    }

    fn begin_array(&mut self, span: Span) -> Result<()> {
        self.inner.begin_array(span)
    }

    fn end_array(&mut self) -> Result<()> {
        self.inner.end_array()
    }

    fn begin_table(
        &mut self,
        fields: Option<&[String]>,
        types: Option<&[String]>,
        span: Span,
    ) -> Result<()> {
        // Validate field names if present
        if let Some(fields) = fields {
            for field in fields {
                self.validate_key(field, span)?;
            }
        }
        self.inner.begin_table(fields, types, span)
    }

    fn end_table(&mut self) -> Result<()> {
        self.inner.end_table()
    }

    fn begin_row(&mut self) -> Result<()> {
        self.inner.begin_row()
    }

    fn end_row(&mut self) -> Result<()> {
        self.inner.end_row()
    }
}

impl SdnHandler for SafeKeyHandler {
    type Output = SdnValue;

    fn finish(self) -> Result<SdnValue> {
        self.inner.finish()
    }
}

impl Default for SafeKeyHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rejects_proto() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        let result = handler.dict_key("__proto__", Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_rejects_constructor() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        let result = handler.dict_key("constructor", Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_rejects_path_traversal() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        assert!(handler.dict_key("../../etc/passwd", Span::default()).is_err());
        assert!(handler.dict_key("/etc/passwd", Span::default()).is_err());
        assert!(handler.dict_key("..\\windows", Span::default()).is_err());
    }

    #[test]
    fn test_rejects_control_chars() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        let result = handler.dict_key("key\nwith\nnewlines", Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_accepts_safe_keys() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("name", Span::default()).unwrap();
        handler.on_string("Alice", Span::default()).unwrap();
        handler.dict_key("user_id", Span::default()).unwrap();
        handler.on_int(42, Span::default()).unwrap();
        handler.end_dict().unwrap();
        let value = handler.finish().unwrap();
        assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
    }

    #[test]
    fn test_validates_table_fields() {
        let mut handler = SafeKeyHandler::new();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("data", Span::default()).unwrap();
        let fields = vec!["__proto__".to_string()];
        let result = handler.begin_table(Some(&fields), None, Span::default());
        assert!(result.is_err());
    }
}
