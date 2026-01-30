//! Jump statement parsing
//!
//! This module handles parsing of jump statements including:
//! - return
//! - break
//! - continue
//! - pass

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    pub(crate) fn parse_return(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Return)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Return(ReturnStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_break(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Break)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Break(BreakStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_continue(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Continue)?;

        Ok(Node::Continue(ContinueStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
        }))
    }

    pub(crate) fn parse_pass(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Pass)?;

        Ok(Node::Pass(PassStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
        }))
    }

    pub(crate) fn parse_skip(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Skip)?;

        // Check for block form (skip:) vs standalone (skip)
        let body = if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            let block = self.parse_block()?;
            SkipBody::Block(block)
        } else {
            SkipBody::Standalone
        };

        Ok(Node::Skip(SkipStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }
}
