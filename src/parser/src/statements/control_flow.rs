//! Control flow statement parsing
//!
//! This module handles parsing of control flow statements including:
//! - if/elif/else
//! - for loops
//! - while loops
//! - infinite loops
//! - context and with statements
//! - match statements

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};
use crate::Parser;

impl<'a> Parser<'a> {
    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let then_block = self.parse_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let elif_condition = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_block()?;
            elif_branches.push((elif_condition, elif_block));
        }

        let else_block = if self.check(&TokenKind::Else) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            Some(self.parse_block()?)
        } else {
            None
        };

        Ok(Node::If(IfStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            then_block,
            elif_branches,
            else_block,
        }))
    }

    pub(crate) fn parse_for(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;

        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::For(ForStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            iterable,
            body,
        }))
    }

    pub(crate) fn parse_while(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::While(WhileStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            body,
        }))
    }

    pub(crate) fn parse_loop(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Loop)?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Loop(LoopStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }

    pub(crate) fn parse_context(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        let context = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Context(ContextStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            context,
            body,
        }))
    }

    pub(crate) fn parse_with(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::With)?;

        let mut resource = self.parse_expression()?;
        let mut alias_from_cast: Option<String> = None;
        // Handle "with expr as name:" where "as name" was parsed as a type cast
        // We detect this by checking if target_type is a simple lowercase identifier (variable name)
        // rather than an actual type (which would be capitalized or a primitive like i64, str, etc.)
        if let Expr::Cast { expr, target_type } = resource.clone() {
            if let Type::Simple(type_name) = target_type {
                // Check if it looks like a variable name (lowercase first char) rather than a type
                let first_char = type_name.chars().next().unwrap_or('A');
                let is_primitive = matches!(type_name.as_str(),
                    "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" |
                    "f32" | "f64" | "bool" | "str" | "nil" | "char");
                if first_char.is_lowercase() && !is_primitive {
                    alias_from_cast = Some(type_name);
                    resource = *expr;
                }
            }
        }

        // Optional "as name"
        let name = if self.check(&TokenKind::As) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            alias_from_cast
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::With(WithStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            resource,
            name,
            body,
        }))
    }

    pub(crate) fn parse_match_stmt(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Match)?;

        let subject = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut arms = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            arms.push(self.parse_match_arm()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Match(MatchStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            subject,
            arms,
        }))
    }

    pub(crate) fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;
        if self.check(&TokenKind::Case) {
            self.advance();
        }
        let pattern = self.parse_pattern()?;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        let body = if self.check(&TokenKind::FatArrow) {
            self.advance();
            // Body can be single expression or block
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else if self.check(&TokenKind::Colon) {
            self.advance();
            self.parse_block()?
        } else {
            return Err(ParseError::unexpected_token(
                "match arm",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        Ok(MatchArm {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            guard,
            body,
        })
    }
}
