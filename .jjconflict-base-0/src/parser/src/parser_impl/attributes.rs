//! Attribute and decorator parsing
//!
//! This module handles parsing of attributes (#[...]) and decorators (@...).

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

impl<'a> Parser<'a> {
    /// Parse a single attribute: #[name] or #[name = value] or #[name(args)]
    pub(super) fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Hash)?;
        self.expect(&TokenKind::LBracket)?;

        // Parse the attribute name - accept identifiers and some keywords
        let name = match &self.current.kind {
            TokenKind::Identifier(s) => {
                let name = s.clone();
                self.advance();
                name
            }
            // Accept 'allow' keyword as attribute name (used in architecture rules)
            // Note: 'deny', 'warn', 'test', 'inline' are identifiers, not keywords
            TokenKind::Allow => {
                self.advance();
                "allow".to_string()
            }
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier or attribute keyword (allow)",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };

        // Check for value: #[name = value]
        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // Check for arguments: #[name(arg1, arg2)]
        let args = self.parse_optional_paren_args()?;

        self.expect(&TokenKind::RBracket)?;

        Ok(Attribute {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            value,
            args,
        })
    }

    /// Parse a single decorator: @name or @name(args)
    /// Also handles @async which uses a keyword instead of identifier.
    /// Supports named arguments: @bounds(default="return", strict=true)
    pub(super) fn parse_decorator(&mut self) -> Result<Decorator, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Handle keywords specially since they can be decorator names
        let name = if self.check(&TokenKind::Async) {
            self.advance();
            Expr::Identifier("async".to_string())
        } else if self.check(&TokenKind::Bounds) {
            self.advance();
            Expr::Identifier("bounds".to_string())
        } else {
            // Parse the decorator name (can be dotted: @module.decorator)
            self.parse_primary()?
        };

        // Check for arguments: @decorator(arg1, arg2) or @decorator(name=value)
        let args = if self.check(&TokenKind::LParen) {
            Some(self.parse_arguments()?)
        } else {
            None
        };

        Ok(Decorator {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            args,
        })
    }

    /// Parse optional parenthesized argument list: `(arg1, arg2, ...)`
    pub(super) fn parse_optional_paren_args(&mut self) -> Result<Option<Vec<Expr>>, ParseError> {
        if self.check(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) {
                args.push(self.parse_expression()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Ok(Some(args))
        } else {
            Ok(None)
        }
    }
}
