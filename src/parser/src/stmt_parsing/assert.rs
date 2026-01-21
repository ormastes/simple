//! Assert, Assume, and Admit statement parsing
//!
//! This module handles parsing of verification statements:
//! - assert condition
//! - assert condition, "message"
//! - assume condition
//! - assume condition, "message"
//! - admit condition
//! - admit condition, "reason"

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    /// Parse a string message from current token (used by assert/assume/admit)
    fn parse_string_message(&mut self) -> Result<String, ParseError> {
        match &self.current.kind {
            TokenKind::String(s) | TokenKind::RawString(s) => {
                let msg = s.clone();
                self.advance();
                Ok(msg)
            }
            TokenKind::FString(parts) => {
                // For f-strings, we extract the literal parts and join them
                // This is a simplified approach - complex interpolation won't work
                use crate::token::FStringToken;
                let msg = parts
                    .iter()
                    .filter_map(|part| match part {
                        FStringToken::Literal(s) => Some(s.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
                    .join("");
                self.advance();
                Ok(msg)
            }
            _ => Err(ParseError::syntax_error_with_span(
                "expected string message",
                self.current.span,
            )),
        }
    }

    /// Parse an optional message after comma
    fn parse_optional_message(&mut self, context: &str) -> Result<Option<String>, ParseError> {
        if self.check(&TokenKind::Comma) {
            self.advance(); // consume comma
            self.parse_string_message()
                .map(Some)
                .map_err(|_| ParseError::syntax_error_with_span(
                    format!("expected string message after comma in {}", context),
                    self.current.span,
                ))
        } else {
            Ok(None)
        }
    }

    /// Parse an assert statement
    /// assert condition
    /// assert condition, "message"
    pub(crate) fn parse_assert(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume 'assert' keyword
        if self.check(&TokenKind::Assert) {
            self.advance();
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected 'assert'",
                self.current.span,
            ));
        }

        // Parse the condition expression
        let condition = self.parse_expression()?;

        // Check for optional message
        let message = self.parse_optional_message("assert")?;

        Ok(Node::Assert(AssertStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            condition,
            message,
        }))
    }

    /// Parse an assume statement
    /// assume condition
    /// assume condition, "message"
    pub(crate) fn parse_assume(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume 'assume' keyword
        if self.check(&TokenKind::Assume) {
            self.advance();
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected 'assume'",
                self.current.span,
            ));
        }

        // Parse the condition expression
        let condition = self.parse_expression()?;

        // Check for optional message
        let message = self.parse_optional_message("assume")?;

        Ok(Node::Assume(AssumeStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            condition,
            message,
        }))
    }

    /// Parse an admit statement
    /// admit condition
    /// admit condition, "reason"
    pub(crate) fn parse_admit(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume 'admit' keyword
        if self.check(&TokenKind::Admit) {
            self.advance();
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected 'admit'",
                self.current.span,
            ));
        }

        // Parse the condition expression
        let condition = self.parse_expression()?;

        // Check for optional message (reason for admission)
        let message = self.parse_optional_message("admit")?;

        Ok(Node::Admit(AdmitStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            condition,
            message,
        }))
    }
}
