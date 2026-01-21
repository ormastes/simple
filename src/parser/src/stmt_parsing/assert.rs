//! Assert statement parsing
//!
//! This module handles parsing of assert statements:
//! - assert condition
//! - assert condition, "message"

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
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

        // Check for optional message (comma followed by string)
        // Note: In Simple, double-quoted strings are FStrings (interpolated)
        // We accept any string type here
        let message = if self.check(&TokenKind::Comma) {
            self.advance(); // consume comma
            match &self.current.kind {
                TokenKind::String(s) | TokenKind::RawString(s) => {
                    let msg = s.clone();
                    self.advance();
                    Some(msg)
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
                    Some(msg)
                }
                _ => {
                    return Err(ParseError::syntax_error_with_span(
                        "expected string message after comma in assert",
                        self.current.span,
                    ));
                }
            }
        } else {
            None
        };

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
}
