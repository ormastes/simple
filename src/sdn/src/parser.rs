//! SDN parser - one-pass LL(2) parser for SDN documents.

use crate::error::{Result, SdnError, Span};
use crate::lexer::{Lexer, Token, TokenKind};
use crate::value::SdnValue;
use indexmap::IndexMap;
use std::collections::HashMap;

/// SDN parser state.
pub struct Parser<'a> {
    tokens: Vec<Token>,
    pos: usize,
    /// Original source (preserved for error messages)
    #[allow(dead_code)]
    source: &'a str,
    /// Span tracking: maps path to source location
    spans: HashMap<String, Span>,
    /// Current path being parsed (for span tracking)
    current_path: Vec<String>,
}

impl<'a> Parser<'a> {
    /// Create a new parser from source.
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize();
        Self {
            tokens,
            pos: 0,
            source,
            spans: HashMap::new(),
            current_path: Vec::new(),
        }
    }

    /// Parse the document into an SdnValue (typically a Dict).
    pub fn parse(&mut self) -> Result<SdnValue> {
        let mut root = IndexMap::new();

        while !self.is_at_end() {
            self.skip_newlines();
            if self.is_at_end() {
                break;
            }

            // Parse top-level statement
            if let Some((key, value)) = self.parse_statement()? {
                root.insert(key, value);
            }
        }

        Ok(SdnValue::Dict(root))
    }

    /// Parse the document and return both the value tree and span mappings.
    /// Spans map from path (e.g., "server.port") to source location.
    pub fn parse_with_spans(&mut self) -> Result<(SdnValue, HashMap<String, Span>)> {
        let value = self.parse()?;
        let spans = std::mem::take(&mut self.spans);
        Ok((value, spans))
    }

    /// Get the current path as a string (e.g., "server.port").
    fn get_current_path(&self) -> String {
        self.current_path.join(".")
    }

    /// Record a span for the current path.
    fn record_span(&mut self, span: Span) {
        if !self.current_path.is_empty() {
            let path = self.get_current_path();
            self.spans.insert(path, span);
        }
    }

    /// Push a key onto the current path.
    fn push_path(&mut self, key: String) {
        self.current_path.push(key);
    }

    /// Pop a key from the current path.
    fn pop_path(&mut self) {
        self.current_path.pop();
    }

    /// Parse a single statement.
    fn parse_statement(&mut self) -> Result<Option<(String, SdnValue)>> {
        self.skip_newlines();

        if self.is_at_end() {
            return Ok(None);
        }

        // Record starting position for span
        let start_pos = self.pos;
        let start_span = if start_pos < self.tokens.len() {
            self.tokens[start_pos].span
        } else {
            Span::default()
        };

        // Must start with an identifier
        let name = self.expect_identifier()?;

        // Push this key onto the path
        self.push_path(name.clone());

        // Check what follows
        let result = match self.peek_kind() {
            Some(TokenKind::Colon) => {
                self.advance();
                self.parse_colon_stmt(name)
            }
            Some(TokenKind::Equals) => {
                self.advance();
                let value = self.parse_inline_value()?;
                self.skip_newlines();
                Ok(Some((name, value)))
            }
            Some(TokenKind::Pipe) => self.parse_named_table(name),
            _ => {
                let span = self.current_span();
                Err(SdnError::syntax_error_with_span(
                    format!("Expected ':', '=', or '|' after identifier '{}'", name),
                    span,
                ))
            }
        };

        // Record span if successful
        if result.is_ok() {
            let end_span = if self.pos > 0 && self.pos <= self.tokens.len() {
                self.tokens[self.pos - 1].span
            } else {
                start_span
            };
            let merged_span = start_span.merge(end_span);
            self.record_span(merged_span);
        }

        // Pop the path
        self.pop_path();

        result
    }

    /// Parse statement after `:`.
    fn parse_colon_stmt(&mut self, name: String) -> Result<Option<(String, SdnValue)>> {
        match self.peek_kind() {
            Some(TokenKind::Table) => {
                // Typed table
                self.parse_typed_table(name)
            }
            Some(TokenKind::Newline) | Some(TokenKind::Indent) => {
                // Block form
                self.skip_newlines();
                if matches!(self.peek_kind(), Some(TokenKind::Indent)) {
                    self.advance(); // consume INDENT
                    let value = self.parse_block()?;
                    Ok(Some((name, value)))
                } else {
                    // Empty value
                    Ok(Some((name, SdnValue::Null)))
                }
            }
            _ => {
                // Simple value
                let value = self.parse_value()?;
                self.skip_newlines();
                Ok(Some((name, value)))
            }
        }
    }

    /// Parse a block (after INDENT).
    fn parse_block(&mut self) -> Result<SdnValue> {
        self.skip_newlines();

        // Look ahead to determine if this is a dict or array block
        if self.is_dict_block() {
            self.parse_dict_block()
        } else {
            self.parse_array_block()
        }
    }

    /// Check if the current block is a dict (ident: value) or array.
    fn is_dict_block(&self) -> bool {
        // Look for pattern: identifier followed by colon
        if let Some(TokenKind::Identifier(_)) = self.peek_kind() {
            if let Some(TokenKind::Colon) = self.peek_kind_at(1) {
                return true;
            }
        }
        false
    }

    /// Parse a dict block.
    fn parse_dict_block(&mut self) -> Result<SdnValue> {
        let mut dict = IndexMap::new();

        loop {
            self.skip_newlines();

            match self.peek_kind() {
                Some(TokenKind::Dedent) | Some(TokenKind::Eof) | None => {
                    if matches!(self.peek_kind(), Some(TokenKind::Dedent)) {
                        self.advance();
                    }
                    break;
                }
                Some(TokenKind::Identifier(_)) => {
                    let start_pos = self.pos;
                    let start_span = if start_pos < self.tokens.len() {
                        self.tokens[start_pos].span
                    } else {
                        Span::default()
                    };

                    let key = self.expect_identifier()?;
                    self.push_path(key.clone());

                    let result: Result<()> = match self.peek_kind() {
                        Some(TokenKind::Colon) => {
                            self.advance();
                            if let Some((_, value)) = self.parse_colon_stmt(key.clone())? {
                                dict.insert(key, value);
                            }
                            Ok(())
                        }
                        Some(TokenKind::Equals) => {
                            self.advance();
                            let value = self.parse_inline_value()?;
                            dict.insert(key, value);
                            self.skip_newlines();
                            Ok(())
                        }
                        Some(TokenKind::Pipe) => {
                            if let Some((_, value)) = self.parse_named_table(key.clone())? {
                                dict.insert(key, value);
                            }
                            Ok(())
                        }
                        _ => {
                            // Bare identifier as value
                            dict.insert(key.clone(), SdnValue::String(key));
                            self.skip_newlines();
                            Ok(())
                        }
                    };

                    if result.is_ok() {
                        let end_span = if self.pos > 0 && self.pos <= self.tokens.len() {
                            self.tokens[self.pos - 1].span
                        } else {
                            start_span
                        };
                        let merged_span = start_span.merge(end_span);
                        self.record_span(merged_span);
                    }

                    self.pop_path();

                    result?;
                }
                _ => {
                    // Unexpected token in dict block
                    self.advance();
                }
            }
        }

        Ok(SdnValue::Dict(dict))
    }

    /// Parse an array block.
    fn parse_array_block(&mut self) -> Result<SdnValue> {
        let mut arr = Vec::new();

        loop {
            self.skip_newlines();

            match self.peek_kind() {
                Some(TokenKind::Dedent) | Some(TokenKind::Eof) | None => {
                    if matches!(self.peek_kind(), Some(TokenKind::Dedent)) {
                        self.advance();
                    }
                    break;
                }
                _ => {
                    let value = self.parse_value()?;
                    arr.push(value);
                    self.skip_newlines();
                }
            }
        }

        Ok(SdnValue::Array(arr))
    }

    /// Parse a typed table: `name: table{types}`.
    fn parse_typed_table(&mut self, name: String) -> Result<Option<(String, SdnValue)>> {
        self.advance(); // consume 'table'
        self.expect(TokenKind::LBrace)?;

        let mut types = Vec::new();
        loop {
            if matches!(self.peek_kind(), Some(TokenKind::RBrace)) {
                break;
            }
            let type_name = self.expect_identifier()?;
            types.push(type_name);
            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenKind::RBrace)?;

        // Check for short form (=) or long form (newline + indent)
        let rows = match self.peek_kind() {
            Some(TokenKind::Equals) => {
                self.advance();
                self.parse_inline_tuple_list()?
            }
            Some(TokenKind::Newline) | Some(TokenKind::Indent) => {
                self.skip_newlines();
                if matches!(self.peek_kind(), Some(TokenKind::Indent)) {
                    self.advance();
                    self.parse_table_rows(types.len())?
                } else {
                    Vec::new()
                }
            }
            _ => Vec::new(),
        };

        Ok(Some((
            name,
            SdnValue::Table {
                fields: None,
                types: Some(types),
                rows,
            },
        )))
    }

    /// Parse a named table: `name |fields|`.
    fn parse_named_table(&mut self, name: String) -> Result<Option<(String, SdnValue)>> {
        self.expect(TokenKind::Pipe)?;

        let mut fields = Vec::new();
        loop {
            if matches!(self.peek_kind(), Some(TokenKind::Pipe)) {
                break;
            }
            let field = self.expect_identifier()?;
            fields.push(field);
            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(TokenKind::Pipe)?;

        // Check for inline row or block rows
        let rows = match self.peek_kind() {
            Some(TokenKind::Newline) | Some(TokenKind::Indent) => {
                self.skip_newlines();
                if matches!(self.peek_kind(), Some(TokenKind::Indent)) {
                    self.advance();
                    self.parse_table_rows(fields.len())?
                } else {
                    Vec::new()
                }
            }
            _ => {
                // Inline single row
                let row = self.parse_table_row(fields.len())?;
                self.skip_newlines();
                vec![row]
            }
        };

        Ok(Some((
            name,
            SdnValue::Table {
                fields: Some(fields),
                types: None,
                rows,
            },
        )))
    }

    /// Parse table rows in block form.
    fn parse_table_rows(&mut self, expected_cols: usize) -> Result<Vec<Vec<SdnValue>>> {
        let mut rows = Vec::new();

        loop {
            self.skip_newlines();

            match self.peek_kind() {
                Some(TokenKind::Dedent) | Some(TokenKind::Eof) | None => {
                    if matches!(self.peek_kind(), Some(TokenKind::Dedent)) {
                        self.advance();
                    }
                    break;
                }
                _ => {
                    let row = self.parse_table_row(expected_cols)?;
                    rows.push(row);
                    self.skip_newlines();
                }
            }
        }

        Ok(rows)
    }

    /// Parse a single table row.
    fn parse_table_row(&mut self, expected_cols: usize) -> Result<Vec<SdnValue>> {
        let mut row = Vec::new();

        loop {
            if self.is_at_end()
                || matches!(
                    self.peek_kind(),
                    Some(TokenKind::Newline) | Some(TokenKind::Dedent)
                )
            {
                break;
            }

            // Handle empty values (consecutive commas or trailing comma)
            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                // Empty value - treat as empty string
                row.push(SdnValue::String(String::new()));
                self.advance();
                continue;
            }

            let value = self.parse_value()?;
            row.push(value);

            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }

        if row.len() != expected_cols && expected_cols > 0 {
            return Err(SdnError::InvalidTableRow {
                expected: expected_cols,
                found: row.len(),
            });
        }

        Ok(row)
    }

    /// Parse inline tuple list: `[(v1, v2), (v3, v4)]`.
    fn parse_inline_tuple_list(&mut self) -> Result<Vec<Vec<SdnValue>>> {
        self.expect(TokenKind::LBracket)?;

        let mut rows = Vec::new();

        loop {
            if matches!(self.peek_kind(), Some(TokenKind::RBracket)) {
                break;
            }

            self.expect(TokenKind::LParen)?;
            let mut row = Vec::new();
            loop {
                if matches!(self.peek_kind(), Some(TokenKind::RParen)) {
                    break;
                }
                let value = self.parse_value()?;
                row.push(value);
                if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                    self.advance();
                } else {
                    break;
                }
            }
            self.expect(TokenKind::RParen)?;
            rows.push(row);

            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }

        self.expect(TokenKind::RBracket)?;
        Ok(rows)
    }

    /// Parse an inline value (dict or array with `=`).
    fn parse_inline_value(&mut self) -> Result<SdnValue> {
        match self.peek_kind() {
            Some(TokenKind::LBrace) => self.parse_inline_dict(),
            Some(TokenKind::LBracket) => self.parse_inline_array(),
            _ => self.parse_value(),
        }
    }

    /// Parse inline dict: `{k: v, k: v}`.
    fn parse_inline_dict(&mut self) -> Result<SdnValue> {
        self.expect(TokenKind::LBrace)?;

        let mut dict = IndexMap::new();

        loop {
            if matches!(self.peek_kind(), Some(TokenKind::RBrace)) {
                break;
            }

            let key = self.expect_identifier()?;
            self.expect(TokenKind::Colon)?;
            let value = self.parse_value()?;
            dict.insert(key, value);

            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        Ok(SdnValue::Dict(dict))
    }

    /// Parse inline array: `[v, v, v]`.
    fn parse_inline_array(&mut self) -> Result<SdnValue> {
        self.expect(TokenKind::LBracket)?;

        let mut arr = Vec::new();

        loop {
            if matches!(self.peek_kind(), Some(TokenKind::RBracket)) {
                break;
            }

            let value = self.parse_value()?;
            arr.push(value);

            if matches!(self.peek_kind(), Some(TokenKind::Comma)) {
                self.advance();
            } else {
                break;
            }
        }

        self.expect(TokenKind::RBracket)?;
        Ok(SdnValue::Array(arr))
    }

    /// Parse a single value.
    fn parse_value(&mut self) -> Result<SdnValue> {
        match self.peek_kind() {
            Some(TokenKind::Integer(i)) => {
                let value = i;
                self.advance();
                Ok(SdnValue::Int(value))
            }
            Some(TokenKind::Float(f)) => {
                let value = f;
                self.advance();
                Ok(SdnValue::Float(value))
            }
            Some(TokenKind::String(s)) => {
                let value = s.clone();
                self.advance();
                Ok(SdnValue::String(value))
            }
            Some(TokenKind::Bool(b)) => {
                let value = b;
                self.advance();
                Ok(SdnValue::Bool(value))
            }
            Some(TokenKind::Null) => {
                self.advance();
                Ok(SdnValue::Null)
            }
            Some(TokenKind::Identifier(s)) => {
                // Bare string
                let value = s.clone();
                self.advance();
                Ok(SdnValue::String(value))
            }
            Some(TokenKind::LBrace) => self.parse_inline_dict(),
            Some(TokenKind::LBracket) => self.parse_inline_array(),
            _ => {
                let span = self.current_span();
                Err(SdnError::syntax_error_with_span("Expected value", span))
            }
        }
    }

    // === Helper methods ===

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn peek_kind(&self) -> Option<TokenKind> {
        self.peek().map(|t| t.kind.clone())
    }

    fn peek_kind_at(&self, offset: usize) -> Option<TokenKind> {
        self.tokens.get(self.pos + offset).map(|t| t.kind.clone())
    }

    fn advance(&mut self) -> Option<&Token> {
        if self.pos < self.tokens.len() {
            let token = &self.tokens[self.pos];
            self.pos += 1;
            Some(token)
        } else {
            None
        }
    }

    fn is_at_end(&self) -> bool {
        matches!(self.peek_kind(), Some(TokenKind::Eof) | None)
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek_kind(), Some(TokenKind::Newline)) {
            self.advance();
        }
    }

    fn current_span(&self) -> Span {
        self.peek().map(|t| t.span).unwrap_or_default()
    }

    fn expect(&mut self, expected: TokenKind) -> Result<()> {
        match self.peek_kind() {
            Some(ref kind) if std::mem::discriminant(kind) == std::mem::discriminant(&expected) => {
                self.advance();
                Ok(())
            }
            Some(ref kind) => Err(SdnError::unexpected_token(
                expected.name(),
                kind.name(),
                self.current_span(),
            )),
            None => Err(SdnError::UnexpectedEof { span: None }),
        }
    }

    fn expect_identifier(&mut self) -> Result<String> {
        match self.peek_kind() {
            Some(TokenKind::Identifier(s)) => {
                let name = s.clone();
                self.advance();
                Ok(name)
            }
            Some(ref kind) => Err(SdnError::unexpected_token(
                "identifier",
                kind.name(),
                self.current_span(),
            )),
            None => Err(SdnError::UnexpectedEof { span: None }),
        }
    }
}

/// Parse SDN source into a value tree.
pub fn parse(source: &str) -> Result<SdnValue> {
    let mut parser = Parser::new(source);
    parser.parse()
}

/// Parse SDN file.
pub fn parse_file(path: &std::path::Path) -> Result<SdnValue> {
    let source = std::fs::read_to_string(path)?;
    parse(&source)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_value() {
        let src = "name: Alice";
        let result = parse(src).unwrap();
        assert_eq!(result.get("name").and_then(|v| v.as_str()), Some("Alice"));
    }

    #[test]
    fn test_multiple_values() {
        let src = "name: Alice\nage: 30\nactive: true";
        let result = parse(src).unwrap();
        assert_eq!(result.get("name").and_then(|v| v.as_str()), Some("Alice"));
        assert_eq!(result.get("age").and_then(|v| v.as_i64()), Some(30));
        assert_eq!(result.get("active").and_then(|v| v.as_bool()), Some(true));
    }

    #[test]
    fn test_inline_dict() {
        let src = "point = {x: 10, y: 20}";
        let result = parse(src).unwrap();
        let point = result.get("point").unwrap();
        assert_eq!(point.get("x").and_then(|v| v.as_i64()), Some(10));
        assert_eq!(point.get("y").and_then(|v| v.as_i64()), Some(20));
    }

    #[test]
    fn test_inline_array() {
        let src = "names = [Alice, Bob, Carol]";
        let result = parse(src).unwrap();
        let names = result.get("names").unwrap().as_array().unwrap();
        assert_eq!(names.len(), 3);
        assert_eq!(names[0].as_str(), Some("Alice"));
    }

    #[test]
    fn test_block_dict() {
        let src = "server:\n    host: localhost\n    port: 8080";
        let result = parse(src).unwrap();
        let server = result.get("server").unwrap();
        assert_eq!(
            server.get("host").and_then(|v| v.as_str()),
            Some("localhost")
        );
        assert_eq!(server.get("port").and_then(|v| v.as_i64()), Some(8080));
    }

    #[test]
    fn test_block_array() {
        let src = "features:\n    auth\n    logging\n    metrics";
        let result = parse(src).unwrap();
        let features = result.get("features").unwrap().as_array().unwrap();
        assert_eq!(features.len(), 3);
        assert_eq!(features[0].as_str(), Some("auth"));
    }

    #[test]
    fn test_named_table() {
        let src = "users |id, name|\n    1, Alice\n    2, Bob";
        let result = parse(src).unwrap();
        let users = result.get("users").unwrap();
        assert!(users.is_table());
    }

    #[test]
    fn test_typed_table() {
        let src = "coords: table{i32, i32} = [(10, 20), (30, 40)]";
        let result = parse(src).unwrap();
        let coords = result.get("coords").unwrap();
        assert!(coords.is_table());
    }

    #[test]
    fn test_nested_structure() {
        let src = "database:\n    primary:\n        host: db1.example.com\n        port: 5432";
        let result = parse(src).unwrap();
        let host = result
            .get_path("database.primary.host")
            .and_then(|v| v.as_str());
        assert_eq!(host, Some("db1.example.com"));
    }

    #[test]
    fn test_quoted_string() {
        let src = "message: \"Hello, World!\"";
        let result = parse(src).unwrap();
        assert_eq!(
            result.get("message").and_then(|v| v.as_str()),
            Some("Hello, World!")
        );
    }

    #[test]
    fn test_float_value() {
        let src = "ratio: 3.15";
        let result = parse(src).unwrap();
        assert!((result.get("ratio").and_then(|v| v.as_f64()).unwrap() - 3.15).abs() < 0.001);
    }

    #[test]
    fn test_null_value() {
        let src = "empty: null";
        let result = parse(src).unwrap();
        assert!(result.get("empty").unwrap().is_null());
    }

    #[test]
    fn test_comment() {
        let src = "# This is a comment\nname: Alice";
        let result = parse(src).unwrap();
        assert_eq!(result.get("name").and_then(|v| v.as_str()), Some("Alice"));
    }

    #[test]
    fn test_table_with_empty_field() {
        let src = "data |a, b, c|\n    1, , 3";
        let result = parse(src).unwrap();
        if let SdnValue::Table { rows, .. } = result.get("data").unwrap() {
            assert_eq!(rows.len(), 1);
            assert_eq!(rows[0].len(), 3);
            assert_eq!(rows[0][0].as_i64(), Some(1));
            assert_eq!(rows[0][1].as_str(), Some("")); // Empty field
            assert_eq!(rows[0][2].as_i64(), Some(3));
        } else {
            panic!("Expected table");
        }
    }

    #[test]
    fn test_table_with_empty_field_from_file_format() {
        // Same content as would be in a file (with trailing newline)
        let src = "data |a, b, c|\n    1, , 3\n";
        let result = parse(src).unwrap();
        if let SdnValue::Table { rows, .. } = result.get("data").unwrap() {
            assert_eq!(rows.len(), 1);
            assert_eq!(rows[0].len(), 3);
            assert_eq!(rows[0][0].as_i64(), Some(1));
            assert_eq!(rows[0][1].as_str(), Some("")); // Empty field
            assert_eq!(rows[0][2].as_i64(), Some(3));
        } else {
            panic!("Expected table");
        }
    }

    #[test]
    fn test_table_with_quoted_string_containing_comma() {
        let src = r#"data |id, name, desc|
    1, Test, "Hello, World""#;
        let result = parse(src).unwrap();
        if let SdnValue::Table { rows, .. } = result.get("data").unwrap() {
            assert_eq!(rows.len(), 1);
            assert_eq!(rows[0].len(), 3);
            assert_eq!(rows[0][2].as_str(), Some("Hello, World"));
        } else {
            panic!("Expected table");
        }
    }
}
