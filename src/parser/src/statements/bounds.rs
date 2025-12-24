//! Bounds clause parsing for @simd kernels
//!
//! Parses the trailing `bounds:` block that specifies bounds event handlers.

use crate::ast::{BoundsAtom, BoundsBlock, BoundsCase, BoundsKind, BoundsPattern};
use crate::error::ParseError;
use crate::token::{Span, TokenKind};
use crate::parser_impl::core::Parser;

impl Parser<'_> {
    /// Parse optional bounds: block after @simd function body
    /// Called after parsing function body, before next declaration
    pub(crate) fn parse_bounds_block(&mut self) -> Result<Option<BoundsBlock>, ParseError> {
        // Check for bounds keyword
        if !self.check(&TokenKind::Bounds) {
            return Ok(None);
        }

        let start_span = self.current.span;
        self.advance(); // consume 'bounds'
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut cases = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            cases.push(self.parse_bounds_case()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Some(BoundsBlock {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            cases,
        }))
    }

    /// Parse single bounds case: pattern: body
    fn parse_bounds_case(&mut self) -> Result<BoundsCase, ParseError> {
        let start_span = self.current.span;
        let pattern = self.parse_bounds_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(BoundsCase {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            body,
        })
    }

    /// Parse bounds pattern (with boolean composition)
    fn parse_bounds_pattern(&mut self) -> Result<BoundsPattern, ParseError> {
        self.parse_bounds_or()
    }

    /// Parse OR: pattern || pattern
    fn parse_bounds_or(&mut self) -> Result<BoundsPattern, ParseError> {
        let mut left = self.parse_bounds_and()?;

        // Check for || (two pipes) or 'or' keyword
        while self.check(&TokenKind::Or) || self.is_double_pipe() {
            if self.is_double_pipe() {
                self.advance(); // consume first |
                self.advance(); // consume second |
            } else {
                self.advance(); // consume 'or'
            }
            let right = self.parse_bounds_and()?;
            left = BoundsPattern::Or(Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    /// Parse AND: pattern && pattern
    fn parse_bounds_and(&mut self) -> Result<BoundsPattern, ParseError> {
        let mut left = self.parse_bounds_primary()?;

        // Check for && (two ampersands) or 'and' keyword
        while self.check(&TokenKind::And) || self.is_double_amp() {
            if self.is_double_amp() {
                self.advance(); // consume first &
                self.advance(); // consume second &
            } else {
                self.advance(); // consume 'and'
            }
            let right = self.parse_bounds_primary()?;
            left = BoundsPattern::And(Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    /// Parse primary: atom, parenthesized, or default
    fn parse_bounds_primary(&mut self) -> Result<BoundsPattern, ParseError> {
        // Check for default catch-all: _ (underscore not followed by dot)
        if self.check(&TokenKind::Underscore) {
            // Look ahead to see if next token is a dot
            if !self.peek_is(&TokenKind::Dot) {
                self.advance(); // consume _
                return Ok(BoundsPattern::Default);
            }
        }

        // Check for parenthesized
        if self.check(&TokenKind::LParen) {
            self.advance();
            let inner = self.parse_bounds_pattern()?;
            self.expect(&TokenKind::RParen)?;
            return Ok(BoundsPattern::Paren(Box::new(inner)));
        }

        // Parse bounds atom: _.<var>.<kind>
        self.parse_bounds_atom()
    }

    /// Parse bounds atom: _.<variable>.<kind>
    fn parse_bounds_atom(&mut self) -> Result<BoundsPattern, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Underscore)?; // _
        self.expect(&TokenKind::Dot)?;         // .

        // Parse variable name
        let variable = if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            name
        } else {
            return Err(ParseError::unexpected_token(
                "identifier",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Dot)?; // .

        // Parse kind: over or under
        let kind = if self.check_bounds_kind("over") {
            self.advance();
            BoundsKind::Over
        } else if self.check_bounds_kind("under") {
            self.advance();
            BoundsKind::Under
        } else {
            return Err(ParseError::unexpected_token(
                "over or under",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        Ok(BoundsPattern::Atom(BoundsAtom {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            variable,
            kind,
        }))
    }

    /// Check if current token is double pipe ||
    fn is_double_pipe(&mut self) -> bool {
        if !self.check(&TokenKind::Pipe) {
            return false;
        }
        self.peek_is(&TokenKind::Pipe)
    }

    /// Check if current token is double ampersand &&
    fn is_double_amp(&mut self) -> bool {
        if !self.check(&TokenKind::Ampersand) {
            return false;
        }
        self.peek_is(&TokenKind::Ampersand)
    }

    /// Check if current token is an identifier with specific name (for bounds kind)
    fn check_bounds_kind(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier(n) if n == name)
    }
}
