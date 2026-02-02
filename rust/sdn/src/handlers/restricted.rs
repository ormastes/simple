//! Policy enforcement handler
//!
//! This handler wraps another handler and enforces structural policies,
//! such as "no tables allowed" or "flat dict only".

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::handlers::ValueBuilder;
use crate::value::SdnValue;

/// Handler that enforces structural policies
///
/// This handler delegates to an inner handler (typically `ValueBuilder`)
/// but rejects certain structures based on policy.
pub struct RestrictedHandler {
    allow_tables: bool,
    allow_arrays: bool,
    allow_nesting: bool,
    depth: usize,
    inner: ValueBuilder,
}

impl RestrictedHandler {
    /// Create a new RestrictedHandler with default policy (allow everything)
    pub fn new() -> Self {
        Self {
            allow_tables: true,
            allow_arrays: true,
            allow_nesting: true,
            depth: 0,
            inner: ValueBuilder::new(),
        }
    }

    /// Create a handler that only allows flat key-value pairs
    ///
    /// This rejects:
    /// - Tables
    /// - Arrays
    /// - Nested dicts
    pub fn flat_dict_only() -> Self {
        Self {
            allow_tables: false,
            allow_arrays: false,
            allow_nesting: false,
            depth: 0,
            inner: ValueBuilder::new(),
        }
    }

    /// Disable tables (reject any table structures)
    pub fn without_tables(mut self) -> Self {
        self.allow_tables = false;
        self
    }

    /// Disable arrays (reject any array structures)
    pub fn without_arrays(mut self) -> Self {
        self.allow_arrays = false;
        self
    }

    /// Disable nesting (only allow one level of dict)
    pub fn without_nesting(mut self) -> Self {
        self.allow_nesting = false;
        self
    }
}

impl DataHandler for RestrictedHandler {
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

impl OpHandler for RestrictedHandler {
    fn begin_dict(&mut self, span: Span) -> Result<()> {
        if self.depth > 0 && !self.allow_nesting {
            return Err(SdnError::SecurityError {
                message: "Nesting not allowed in this context".to_string(),
                span: Some(span),
            });
        }
        self.depth += 1;
        self.inner.begin_dict(span)
    }

    fn end_dict(&mut self) -> Result<()> {
        self.depth -= 1;
        self.inner.end_dict()
    }

    fn begin_array(&mut self, span: Span) -> Result<()> {
        if !self.allow_arrays {
            return Err(SdnError::SecurityError {
                message: "Arrays not allowed in this context".to_string(),
                span: Some(span),
            });
        }
        self.depth += 1;
        self.inner.begin_array(span)
    }

    fn end_array(&mut self) -> Result<()> {
        self.depth -= 1;
        self.inner.end_array()
    }

    fn begin_table(&mut self, fields: Option<&[String]>, types: Option<&[String]>, span: Span) -> Result<()> {
        if !self.allow_tables {
            return Err(SdnError::SecurityError {
                message: "Tables not allowed in this context".to_string(),
                span: Some(span),
            });
        }
        self.depth += 1;
        self.inner.begin_table(fields, types, span)
    }

    fn end_table(&mut self) -> Result<()> {
        self.depth -= 1;
        self.inner.end_table()
    }

    fn begin_row(&mut self) -> Result<()> {
        self.inner.begin_row()
    }

    fn end_row(&mut self) -> Result<()> {
        self.inner.end_row()
    }

    fn dict_key(&mut self, key: &str, span: Span) -> Result<()> {
        self.inner.dict_key(key, span)
    }
}

impl SdnHandler for RestrictedHandler {
    type Output = SdnValue;

    fn finish(self) -> Result<SdnValue> {
        self.inner.finish()
    }
}

impl Default for RestrictedHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flat_dict_rejects_nesting() {
        let mut handler = RestrictedHandler::flat_dict_only();
        handler.begin_dict(Span::default()).unwrap(); // root dict
        handler.dict_key("server", Span::default()).unwrap();
        let result = handler.begin_dict(Span::default()); // nested dict
        assert!(result.is_err());
    }

    #[test]
    fn test_flat_dict_rejects_arrays() {
        let mut handler = RestrictedHandler::flat_dict_only();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("items", Span::default()).unwrap();
        let result = handler.begin_array(Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_flat_dict_rejects_tables() {
        let mut handler = RestrictedHandler::flat_dict_only();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("data", Span::default()).unwrap();
        let result = handler.begin_table(Some(&[]), None, Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_flat_dict_accepts_primitives() {
        let mut handler = RestrictedHandler::flat_dict_only();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("name", Span::default()).unwrap();
        handler.on_string("Alice", Span::default()).unwrap();
        handler.dict_key("age", Span::default()).unwrap();
        handler.on_int(30, Span::default()).unwrap();
        handler.end_dict().unwrap();
        let value = handler.finish().unwrap();
        assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
    }

    #[test]
    fn test_without_tables() {
        let mut handler = RestrictedHandler::new().without_tables();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("data", Span::default()).unwrap();
        let result = handler.begin_table(Some(&[]), None, Span::default());
        assert!(result.is_err());
    }

    #[test]
    fn test_without_arrays() {
        let mut handler = RestrictedHandler::new().without_arrays();
        handler.begin_dict(Span::default()).unwrap();
        handler.dict_key("items", Span::default()).unwrap();
        let result = handler.begin_array(Span::default());
        assert!(result.is_err());
    }
}
