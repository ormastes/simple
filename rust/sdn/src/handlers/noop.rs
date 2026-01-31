//! Zero-allocation validation handler
//!
//! This handler validates SDN input without building the value tree.
//! It enforces depth limits, size limits, and cell count limits to prevent
//! denial-of-service attacks.

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};

/// Handler that validates without allocating
///
/// This is useful for validating untrusted input before parsing.
/// It tracks nesting depth and cell count to reject malicious input.
pub struct NoopHandler {
    depth: usize,
    max_depth: usize,
    max_string_len: usize,
    max_cell_count: usize,
    cell_count: usize,
}

impl NoopHandler {
    /// Create a new NoopHandler with default limits
    ///
    /// Default limits:
    /// - max_depth: 100
    /// - max_string_len: 1 MB
    /// - max_cell_count: 10 million
    pub fn new() -> Self {
        Self::with_limits(100, 1_048_576, 10_000_000)
    }

    /// Create a NoopHandler with custom limits
    pub fn with_limits(max_depth: usize, max_string_len: usize, max_cell_count: usize) -> Self {
        Self {
            depth: 0,
            max_depth,
            max_string_len,
            max_cell_count,
            cell_count: 0,
        }
    }

    fn check_cell_count(&mut self, span: Span) -> Result<()> {
        self.cell_count += 1;
        if self.cell_count > self.max_cell_count {
            return Err(SdnError::SecurityError {
                message: format!("Cell count exceeds limit: {}", self.max_cell_count),
                span: Some(span),
            });
        }
        Ok(())
    }

    fn check_depth(&self, span: Span) -> Result<()> {
        if self.depth > self.max_depth {
            return Err(SdnError::SecurityError {
                message: format!("Nesting depth exceeds limit: {}", self.max_depth),
                span: Some(span),
            });
        }
        Ok(())
    }
}

impl DataHandler for NoopHandler {
    fn on_null(&mut self, span: Span) -> Result<()> {
        self.check_cell_count(span)
    }

    fn on_bool(&mut self, _value: bool, span: Span) -> Result<()> {
        self.check_cell_count(span)
    }

    fn on_int(&mut self, _value: i64, span: Span) -> Result<()> {
        self.check_cell_count(span)
    }

    fn on_float(&mut self, _value: f64, span: Span) -> Result<()> {
        self.check_cell_count(span)
    }

    fn on_string(&mut self, value: &str, span: Span) -> Result<()> {
        if value.len() > self.max_string_len {
            return Err(SdnError::SecurityError {
                message: format!("String exceeds max length: {} > {}", value.len(), self.max_string_len),
                span: Some(span),
            });
        }
        self.check_cell_count(span)
    }
}

impl OpHandler for NoopHandler {
    fn begin_dict(&mut self, span: Span) -> Result<()> {
        self.depth += 1;
        self.check_depth(span)
    }

    fn end_dict(&mut self) -> Result<()> {
        self.depth -= 1;
        Ok(())
    }

    fn begin_array(&mut self, span: Span) -> Result<()> {
        self.depth += 1;
        self.check_depth(span)
    }

    fn end_array(&mut self) -> Result<()> {
        self.depth -= 1;
        Ok(())
    }

    fn begin_table(
        &mut self,
        _fields: Option<&[String]>,
        _types: Option<&[String]>,
        span: Span,
    ) -> Result<()> {
        self.depth += 1;
        self.check_depth(span)
    }

    fn end_table(&mut self) -> Result<()> {
        self.depth -= 1;
        Ok(())
    }

    fn begin_row(&mut self) -> Result<()> {
        Ok(())
    }

    fn end_row(&mut self) -> Result<()> {
        Ok(())
    }

    fn dict_key(&mut self, _key: &str, _span: Span) -> Result<()> {
        Ok(())
    }
}

impl SdnHandler for NoopHandler {
    type Output = ();

    fn finish(self) -> Result<()> {
        Ok(())
    }
}

impl Default for NoopHandler {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_noop_accepts_valid_depth() {
        let mut noop = NoopHandler::with_limits(3, 1024, 1000);
        assert!(noop.begin_dict(Span::default()).is_ok());
        assert!(noop.begin_dict(Span::default()).is_ok());
        assert!(noop.begin_dict(Span::default()).is_ok());
    }

    #[test]
    fn test_noop_rejects_deep_nesting() {
        let mut noop = NoopHandler::with_limits(3, 1024, 1000);
        assert!(noop.begin_dict(Span::default()).is_ok()); // depth=1
        assert!(noop.begin_dict(Span::default()).is_ok()); // depth=2
        assert!(noop.begin_dict(Span::default()).is_ok()); // depth=3
        assert!(noop.begin_dict(Span::default()).is_err()); // depth=4, exceeds limit
    }

    #[test]
    fn test_noop_rejects_large_string() {
        let mut noop = NoopHandler::with_limits(10, 100, 1000);
        let small = "x".repeat(50);
        let large = "x".repeat(200);
        assert!(noop.on_string(&small, Span::default()).is_ok());
        assert!(noop.on_string(&large, Span::default()).is_err());
    }

    #[test]
    fn test_noop_rejects_cell_count() {
        let mut noop = NoopHandler::with_limits(100, 1024, 5);
        for _ in 0..5 {
            assert!(noop.on_int(1, Span::default()).is_ok());
        }
        assert!(noop.on_int(1, Span::default()).is_err()); // 6th cell
    }

    #[test]
    fn test_noop_depth_tracking() {
        let mut noop = NoopHandler::with_limits(3, 1024, 1000);
        noop.begin_dict(Span::default()).unwrap();
        noop.begin_array(Span::default()).unwrap();
        noop.end_array().unwrap(); // depth=1
        noop.begin_dict(Span::default()).unwrap(); // depth=2
        assert!(noop.begin_dict(Span::default()).is_ok()); // depth=3
    }
}
