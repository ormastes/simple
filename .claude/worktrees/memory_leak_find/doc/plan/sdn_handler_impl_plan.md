# SDN Handler Implementation Plan

**Date:** 2026-01-31
**Design Doc:** `doc/design/sdn_handler_trait_design.md`
**Target:** `rust/sdn/` crate

---

## Overview

Implement trait-based handler architecture for SDN parser to separate data processing from operation processing. This enables security policies, zero-allocation validation, and restricted parsing modes.

---

## Implementation Phases

### Phase 1: Foundation — Add Traits (Non-Breaking)

**Goal:** Add trait definitions without breaking existing API

**Files to Create:**
- `rust/sdn/src/handler.rs` — trait definitions
- `rust/sdn/src/handlers/mod.rs` — handler implementations module
- `rust/sdn/src/handlers/value_builder.rs` — default handler
- `rust/sdn/src/handlers/noop.rs` — validation-only handler

**Tasks:**

#### 1.1: Define Core Traits

Create `rust/sdn/src/handler.rs`:

```rust
//! Handler traits for SDN parsing

use crate::error::{Result, Span};

/// Handles primitive data values during parsing
pub trait DataHandler {
    fn on_null(&mut self, span: Span) -> Result<()>;
    fn on_bool(&mut self, value: bool, span: Span) -> Result<()>;
    fn on_int(&mut self, value: i64, span: Span) -> Result<()>;
    fn on_float(&mut self, value: f64, span: Span) -> Result<()>;
    fn on_string(&mut self, value: &str, span: Span) -> Result<()>;
}

/// Handles structural operations during parsing
pub trait OpHandler {
    fn begin_dict(&mut self, span: Span) -> Result<()>;
    fn dict_key(&mut self, key: &str, span: Span) -> Result<()>;
    fn end_dict(&mut self) -> Result<()>;

    fn begin_array(&mut self, span: Span) -> Result<()>;
    fn end_array(&mut self) -> Result<()>;

    fn begin_table(
        &mut self,
        fields: Option<&[String]>,
        types: Option<&[String]>,
        span: Span,
    ) -> Result<()>;
    fn begin_row(&mut self) -> Result<()>;
    fn end_row(&mut self) -> Result<()>;
    fn end_table(&mut self) -> Result<()>;
}

/// Combined handler trait
pub trait SdnHandler: DataHandler + OpHandler {
    type Output;
    fn finish(self) -> Result<Self::Output>;
}
```

**Test:** Traits compile, no existing code breaks

---

#### 1.2: Implement `ValueBuilder` (Default Handler)

Create `rust/sdn/src/handlers/value_builder.rs`:

```rust
//! Default handler that builds SdnValue tree

use crate::error::{Result, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::value::SdnValue;
use indexmap::IndexMap;

pub struct ValueBuilder {
    stack: Vec<BuilderFrame>,
    root: Option<SdnValue>,
}

enum BuilderFrame {
    Dict {
        map: IndexMap<String, SdnValue>,
        current_key: Option<String>,
    },
    Array {
        items: Vec<SdnValue>,
    },
    Table {
        fields: Option<Vec<String>>,
        types: Option<Vec<String>>,
        rows: Vec<Vec<SdnValue>>,
        current_row: Option<Vec<SdnValue>>,
    },
}

impl ValueBuilder {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            root: None,
        }
    }

    fn push_value(&mut self, value: SdnValue) {
        match self.stack.last_mut() {
            Some(BuilderFrame::Dict { map, current_key }) => {
                if let Some(key) = current_key.take() {
                    map.insert(key, value);
                }
            }
            Some(BuilderFrame::Array { items }) => {
                items.push(value);
            }
            Some(BuilderFrame::Table { current_row: Some(row), .. }) => {
                row.push(value);
            }
            None => {
                self.root = Some(value);
            }
            _ => {}
        }
    }
}

impl DataHandler for ValueBuilder {
    fn on_null(&mut self, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Null);
        Ok(())
    }

    fn on_bool(&mut self, value: bool, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Bool(value));
        Ok(())
    }

    fn on_int(&mut self, value: i64, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Int(value));
        Ok(())
    }

    fn on_float(&mut self, value: f64, _span: Span) -> Result<()> {
        self.push_value(SdnValue::Float(value));
        Ok(())
    }

    fn on_string(&mut self, value: &str, _span: Span) -> Result<()> {
        self.push_value(SdnValue::String(value.to_string()));
        Ok(())
    }
}

impl OpHandler for ValueBuilder {
    fn begin_dict(&mut self, _span: Span) -> Result<()> {
        self.stack.push(BuilderFrame::Dict {
            map: IndexMap::new(),
            current_key: None,
        });
        Ok(())
    }

    fn dict_key(&mut self, key: &str, _span: Span) -> Result<()> {
        if let Some(BuilderFrame::Dict { current_key, .. }) = self.stack.last_mut() {
            *current_key = Some(key.to_string());
        }
        Ok(())
    }

    fn end_dict(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Dict { map, .. }) = self.stack.pop() {
            self.push_value(SdnValue::Dict(map));
        }
        Ok(())
    }

    fn begin_array(&mut self, _span: Span) -> Result<()> {
        self.stack.push(BuilderFrame::Array { items: Vec::new() });
        Ok(())
    }

    fn end_array(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Array { items }) = self.stack.pop() {
            self.push_value(SdnValue::Array(items));
        }
        Ok(())
    }

    fn begin_table(
        &mut self,
        fields: Option<&[String]>,
        types: Option<&[String]>,
        _span: Span,
    ) -> Result<()> {
        self.stack.push(BuilderFrame::Table {
            fields: fields.map(|f| f.to_vec()),
            types: types.map(|t| t.to_vec()),
            rows: Vec::new(),
            current_row: None,
        });
        Ok(())
    }

    fn begin_row(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table { current_row, .. }) = self.stack.last_mut() {
            *current_row = Some(Vec::new());
        }
        Ok(())
    }

    fn end_row(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table { rows, current_row, .. }) = self.stack.last_mut() {
            if let Some(row) = current_row.take() {
                rows.push(row);
            }
        }
        Ok(())
    }

    fn end_table(&mut self) -> Result<()> {
        if let Some(BuilderFrame::Table { fields, types, rows, .. }) = self.stack.pop() {
            self.push_value(SdnValue::Table { fields, types, rows });
        }
        Ok(())
    }
}

impl SdnHandler for ValueBuilder {
    type Output = SdnValue;

    fn finish(self) -> Result<SdnValue> {
        self.root.ok_or_else(|| crate::error::SdnError::ParseError {
            message: "No value parsed".to_string(),
            span: None,
        })
    }
}

impl Default for ValueBuilder {
    fn default() -> Self {
        Self::new()
    }
}
```

**Test:**
```rust
#[test]
fn test_value_builder_basic() {
    let mut builder = ValueBuilder::new();
    builder.begin_dict(Span::default()).unwrap();
    builder.dict_key("name", Span::default()).unwrap();
    builder.on_string("Alice", Span::default()).unwrap();
    builder.end_dict().unwrap();
    let value = builder.finish().unwrap();
    assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
}
```

---

#### 1.3: Implement `NoopHandler` (Validation-Only)

Create `rust/sdn/src/handlers/noop.rs`:

```rust
//! Zero-allocation validation handler

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};

pub struct NoopHandler {
    depth: usize,
    max_depth: usize,
    max_string_len: usize,
    max_cell_count: usize,
    cell_count: usize,
}

impl NoopHandler {
    pub fn new() -> Self {
        Self::with_limits(100, 1_048_576, 10_000_000)
    }

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
            return Err(SdnError::security_error(
                format!("Cell count exceeds limit: {}", self.max_cell_count),
                span,
            ));
        }
        Ok(())
    }

    fn check_depth(&self, span: Span) -> Result<()> {
        if self.depth > self.max_depth {
            return Err(SdnError::security_error(
                format!("Nesting depth exceeds limit: {}", self.max_depth),
                span,
            ));
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
            return Err(SdnError::security_error(
                format!("String exceeds max length: {} > {}", value.len(), self.max_string_len),
                span,
            ));
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

    fn begin_row(&mut self) -> Result<()> { Ok(()) }
    fn end_row(&mut self) -> Result<()> { Ok(()) }
    fn dict_key(&mut self, _key: &str, _span: Span) -> Result<()> { Ok(()) }
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
```

**Test:**
```rust
#[test]
fn test_noop_rejects_deep_nesting() {
    let mut noop = NoopHandler::with_limits(3, 1024, 1000);
    noop.begin_dict(Span::default()).unwrap();
    noop.begin_dict(Span::default()).unwrap();
    noop.begin_dict(Span::default()).unwrap();
    noop.begin_dict(Span::default()).unwrap(); // depth=4, max=3
    assert!(noop.begin_dict(Span::default()).is_err()); // Should fail
}
```

---

#### 1.4: Update `error.rs` for Security Errors

Add to `rust/sdn/src/error.rs`:

```rust
impl SdnError {
    pub fn security_error(message: impl Into<String>, span: Span) -> Self {
        SdnError::SecurityError {
            message: message.into(),
            span: Some(span),
        }
    }

    pub fn is_security_error(&self) -> bool {
        matches!(self, SdnError::SecurityError { .. })
    }
}

// Add to SdnError enum:
#[derive(Debug, Clone, PartialEq)]
pub enum SdnError {
    // ... existing variants
    SecurityError {
        message: String,
        span: Option<Span>,
    },
}
```

---

#### 1.5: Update Module Structure

Edit `rust/sdn/src/lib.rs`:

```rust
mod error;
mod lexer;
mod parser;
mod value;
mod document;
mod handler;  // NEW
mod handlers; // NEW

pub use error::{Result, SdnError, Span};
pub use lexer::{Lexer, Token, TokenKind};
pub use parser::{Parser, parse, parse_file};
pub use value::SdnValue;
pub use document::SdnDocument;
pub use handler::{DataHandler, OpHandler, SdnHandler}; // NEW
pub use handlers::{ValueBuilder, NoopHandler};         // NEW
```

Create `rust/sdn/src/handlers/mod.rs`:

```rust
mod value_builder;
mod noop;

pub use value_builder::ValueBuilder;
pub use noop::NoopHandler;
```

**Test:** `cargo build -p simple-sdn` succeeds

---

### Phase 2: Parser Integration

**Goal:** Modify parser to call handler methods

**Files to Modify:**
- `rust/sdn/src/parser.rs` — refactor to use handlers

**Tasks:**

#### 2.1: Add `parse_with_handler()` Method

Add to `Parser` impl in `rust/sdn/src/parser.rs`:

```rust
impl<'a> Parser<'a> {
    /// Parse with custom handler
    pub fn parse_with_handler<H: SdnHandler>(
        &mut self,
        mut handler: H,
    ) -> Result<H::Output> {
        handler.begin_dict(Span::default())?;

        while !self.is_at_end() {
            self.skip_newlines();
            if self.is_at_end() {
                break;
            }

            self.parse_statement_with_handler(&mut handler)?;
        }

        handler.end_dict()?;
        handler.finish()
    }

    /// Parse existing method now delegates to handler
    pub fn parse(&mut self) -> Result<SdnValue> {
        let handler = ValueBuilder::new();
        self.parse_with_handler(handler)
    }
}
```

---

#### 2.2: Refactor `parse_statement()` to Use Handler

**Before:**
```rust
fn parse_statement(&mut self) -> Result<Option<(String, SdnValue)>>
```

**After:**
```rust
fn parse_statement_with_handler<H: SdnHandler>(
    &mut self,
    handler: &mut H,
) -> Result<()> {
    self.skip_newlines();
    if self.is_at_end() {
        return Ok(());
    }

    let start_span = self.current_span();
    let name = self.expect_identifier()?;

    handler.dict_key(&name, start_span)?;

    match self.peek_kind() {
        Some(TokenKind::Colon) => {
            self.advance();
            self.parse_colon_stmt_with_handler(handler)?;
        }
        Some(TokenKind::Equals) => {
            self.advance();
            self.parse_inline_value_with_handler(handler)?;
        }
        Some(TokenKind::Pipe) => {
            self.parse_named_table_with_handler(handler)?;
        }
        _ => {
            return Err(SdnError::syntax_error_with_span(
                format!("Expected ':', '=', or '|' after identifier '{}'", name),
                self.current_span(),
            ));
        }
    }

    Ok(())
}
```

---

#### 2.3: Refactor Value Parsing Methods

Convert these methods to use handler:
- `parse_value()` → `parse_value_with_handler()`
- `parse_dict_block()` → `parse_dict_block_with_handler()`
- `parse_array_block()` → `parse_array_block_with_handler()`
- `parse_named_table()` → `parse_named_table_with_handler()`

**Example: `parse_value_with_handler()`**

```rust
fn parse_value_with_handler<H: SdnHandler>(
    &mut self,
    handler: &mut H,
) -> Result<()> {
    let span = self.current_span();

    match self.peek_kind() {
        Some(TokenKind::Integer(i)) => {
            self.advance();
            handler.on_int(i, span)?;
        }
        Some(TokenKind::Float(f)) => {
            self.advance();
            handler.on_float(f, span)?;
        }
        Some(TokenKind::String(s)) => {
            let value = s.clone();
            self.advance();
            handler.on_string(&value, span)?;
        }
        Some(TokenKind::Bool(b)) => {
            self.advance();
            handler.on_bool(b, span)?;
        }
        Some(TokenKind::Null) => {
            self.advance();
            handler.on_null(span)?;
        }
        Some(TokenKind::Identifier(s)) => {
            let value = s.clone();
            self.advance();
            handler.on_string(&value, span)?;
        }
        Some(TokenKind::LBrace) => {
            self.parse_inline_dict_with_handler(handler)?;
        }
        Some(TokenKind::LBracket) => {
            self.parse_inline_array_with_handler(handler)?;
        }
        _ => {
            return Err(SdnError::syntax_error_with_span("Expected value", span));
        }
    }

    Ok(())
}
```

**Test:** All existing parser tests still pass

---

### Phase 3: Security Handlers

**Goal:** Add policy enforcement handlers

**Files to Create:**
- `rust/sdn/src/handlers/restricted.rs`
- `rust/sdn/src/handlers/safe_key.rs`

#### 3.1: Restricted Handler

Create `rust/sdn/src/handlers/restricted.rs`:

```rust
//! Policy enforcement handler

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::handlers::ValueBuilder;
use crate::value::SdnValue;

pub struct RestrictedHandler {
    allow_tables: bool,
    allow_arrays: bool,
    allow_nesting: bool,
    depth: usize,
    inner: ValueBuilder,
}

impl RestrictedHandler {
    pub fn new() -> Self {
        Self {
            allow_tables: true,
            allow_arrays: true,
            allow_nesting: true,
            depth: 0,
            inner: ValueBuilder::new(),
        }
    }

    pub fn flat_dict_only() -> Self {
        Self {
            allow_tables: false,
            allow_arrays: false,
            allow_nesting: false,
            depth: 0,
            inner: ValueBuilder::new(),
        }
    }

    pub fn without_tables(mut self) -> Self {
        self.allow_tables = false;
        self
    }

    pub fn without_arrays(mut self) -> Self {
        self.allow_arrays = false;
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
            return Err(SdnError::security_error("Nesting not allowed in this context", span));
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
            return Err(SdnError::security_error("Arrays not allowed in this context", span));
        }
        self.depth += 1;
        self.inner.begin_array(span)
    }

    fn end_array(&mut self) -> Result<()> {
        self.depth -= 1;
        self.inner.end_array()
    }

    fn begin_table(
        &mut self,
        fields: Option<&[String]>,
        types: Option<&[String]>,
        span: Span,
    ) -> Result<()> {
        if !self.allow_tables {
            return Err(SdnError::security_error("Tables not allowed in this context", span));
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
```

---

#### 3.2: Safe Key Handler

Create `rust/sdn/src/handlers/safe_key.rs`:

```rust
//! Handler that rejects dangerous keys

use crate::error::{Result, SdnError, Span};
use crate::handler::{DataHandler, OpHandler, SdnHandler};
use crate::handlers::ValueBuilder;
use crate::value::SdnValue;

pub struct SafeKeyHandler {
    inner: ValueBuilder,
}

impl SafeKeyHandler {
    pub fn new() -> Self {
        Self {
            inner: ValueBuilder::new(),
        }
    }

    fn validate_key(&self, key: &str, span: Span) -> Result<()> {
        // Reject prototype pollution keys
        if matches!(key, "__proto__" | "constructor" | "prototype") {
            return Err(SdnError::security_error(
                format!("Unsafe key rejected: {}", key),
                span,
            ));
        }

        // Reject path traversal
        if key.contains("..") || key.starts_with('/') || key.starts_with('\\') {
            return Err(SdnError::security_error(
                format!("Path traversal rejected: {}", key),
                span,
            ));
        }

        // Reject control characters
        if key.chars().any(|c| c.is_control()) {
            return Err(SdnError::security_error(
                format!("Control characters not allowed in keys: {}", key),
                span,
            ));
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
```

---

### Phase 4: Public API and Tests

**Goal:** Add convenience functions and comprehensive tests

#### 4.1: Add Convenience Functions

Add to `rust/sdn/src/parser.rs`:

```rust
/// Parse untrusted SDN input with validation
pub fn parse_untrusted(source: &str) -> Result<SdnValue> {
    // First pass: validate structure
    let mut parser = Parser::new(source);
    let noop = NoopHandler::with_limits(50, 1_048_576, 1_000_000);
    parser.parse_with_handler(noop)?;

    // Second pass: build tree (already validated)
    let mut parser = Parser::new(source);
    parser.parse()
}

/// Parse configuration file (flat dict only)
pub fn parse_config(source: &str) -> Result<SdnValue> {
    let mut parser = Parser::new(source);
    let handler = RestrictedHandler::flat_dict_only();
    parser.parse_with_handler(handler)
}

/// Parse with safe key validation
pub fn parse_safe(source: &str) -> Result<SdnValue> {
    let mut parser = Parser::new(source);
    let handler = SafeKeyHandler::new();
    parser.parse_with_handler(handler)
}
```

---

#### 4.2: Security Test Suite

Create `rust/sdn/tests/security_tests.rs`:

```rust
use simple_sdn::*;

#[test]
fn test_depth_dos_rejected() {
    // 100-level nesting
    let src = "a:\n".to_string() + &"  b:\n".repeat(100);
    let noop = NoopHandler::with_limits(50, 1024, 1000);
    let mut parser = Parser::new(&src);
    assert!(parser.parse_with_handler(noop).is_err());
}

#[test]
fn test_large_string_rejected() {
    let large_str = "x".repeat(2_000_000); // 2 MB
    let src = format!("data: \"{}\"", large_str);
    let noop = NoopHandler::with_limits(100, 1_048_576, 1000);
    let mut parser = Parser::new(&src);
    assert!(parser.parse_with_handler(noop).is_err());
}

#[test]
fn test_cell_count_dos_rejected() {
    // 100k cells
    let src = "data: [".to_string() + &"1, ".repeat(100_000) + "1]";
    let noop = NoopHandler::with_limits(100, 1024, 10_000);
    let mut parser = Parser::new(&src);
    assert!(parser.parse_with_handler(noop).is_err());
}

#[test]
fn test_proto_pollution_rejected() {
    let src = "__proto__: malicious";
    let handler = SafeKeyHandler::new();
    let mut parser = Parser::new(src);
    assert!(parser.parse_with_handler(handler).is_err());
}

#[test]
fn test_path_traversal_rejected() {
    let src = "../../etc/passwd: secret";
    let handler = SafeKeyHandler::new();
    let mut parser = Parser::new(src);
    assert!(parser.parse_with_handler(handler).is_err());
}

#[test]
fn test_tables_rejected_in_config_mode() {
    let src = "users |id, name|\n  1, Alice";
    assert!(parse_config(src).is_err());
}

#[test]
fn test_nesting_rejected_in_flat_mode() {
    let src = "server:\n  host: localhost";
    let handler = RestrictedHandler::flat_dict_only();
    let mut parser = Parser::new(src);
    assert!(parser.parse_with_handler(handler).is_err());
}

#[test]
fn test_untrusted_parse_valid_input() {
    let src = "name: Alice\nage: 30";
    let value = parse_untrusted(src).unwrap();
    assert_eq!(value.get("name").and_then(|v| v.as_str()), Some("Alice"));
}
```

---

## Testing Checklist

- [ ] All existing parser tests pass
- [ ] `ValueBuilder` produces identical output to old parser
- [ ] `NoopHandler` rejects depth/size attacks
- [ ] `RestrictedHandler` enforces policies
- [ ] `SafeKeyHandler` rejects dangerous keys
- [ ] `parse_untrusted()` works correctly
- [ ] Performance: `NoopHandler` is 5-10x faster than `ValueBuilder`
- [ ] Zero regressions in existing code

---

## Documentation Updates

### Update `rust/sdn/README.md`

Add section:

```markdown
## Security

SDN provides multiple parsing modes for different trust levels:

### Default Parsing (Trusted Input)
```rust
let value = parse("name: Alice")?;
```

### Untrusted Input (Two-Pass Validation)
```rust
let value = parse_untrusted(untrusted_source)?;
// Rejects: deep nesting, large strings, excessive cells
```

### Configuration Files (Flat Structure Only)
```rust
let config = parse_config(config_source)?;
// Rejects: tables, arrays, nesting
```

### Safe Keys (Prevent Injection)
```rust
let value = parse_safe(source)?;
// Rejects: __proto__, constructor, ../, control chars
```

### Custom Policies
```rust
let handler = RestrictedHandler::new().without_tables();
let value = parser.parse_with_handler(handler)?;
```

For security research, see: `doc/research/data_format_parser_security_2026-01-31.md`
```

---

## File Changes Summary

### New Files (13)
1. `rust/sdn/src/handler.rs` — trait definitions
2. `rust/sdn/src/handlers/mod.rs` — module
3. `rust/sdn/src/handlers/value_builder.rs` — default handler
4. `rust/sdn/src/handlers/noop.rs` — validation handler
5. `rust/sdn/src/handlers/restricted.rs` — policy handler
6. `rust/sdn/src/handlers/safe_key.rs` — key validation handler
7. `rust/sdn/tests/security_tests.rs` — security test suite
8. `doc/design/sdn_handler_trait_design.md` — this design doc
9. `doc/plan/sdn_handler_impl_plan.md` — this implementation plan
10. `doc/research/data_format_parser_security_2026-01-31.md` — security research

### Modified Files (3)
1. `rust/sdn/src/lib.rs` — export new modules
2. `rust/sdn/src/error.rs` — add `SecurityError` variant
3. `rust/sdn/src/parser.rs` — refactor to use handlers
4. `rust/sdn/README.md` — document security features

---

## Success Criteria

1. **Backward Compatible:** All existing code works without changes
2. **Zero-Cost:** `ValueBuilder` compiles to same code as current parser
3. **Performance:** `NoopHandler` is measurably faster (benchmark)
4. **Security:** All attack vectors from research doc are mitigated
5. **Tested:** 100% coverage of handler implementations
6. **Documented:** README and doc comments explain usage

---

## Timeline Estimate

| Phase | Tasks | Estimated Time |
|-------|-------|----------------|
| Phase 1 | Traits + ValueBuilder + NoopHandler | 4-6 hours |
| Phase 2 | Parser refactoring | 6-8 hours |
| Phase 3 | Security handlers | 3-4 hours |
| Phase 4 | Tests + docs | 3-4 hours |
| **Total** | | **16-22 hours** |

---

## Next Steps

1. Review this plan with stakeholders
2. Start Phase 1: implement traits and `ValueBuilder`
3. Run existing test suite to ensure no regressions
4. Proceed to Phase 2 only after Phase 1 tests pass

---

## References

- **Design Doc:** `doc/design/sdn_handler_trait_design.md`
- **Security Research:** `doc/research/data_format_parser_security_2026-01-31.md`
- **Current Parser:** `rust/sdn/src/parser.rs`
- **Test Suite:** `rust/sdn/tests/parser_tests.rs`
