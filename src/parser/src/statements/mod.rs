//! Statement parsing module
//!
//! This module contains all statement parsing logic including:
//! - Variable declarations (let, mut let, const, static)
//! - Control flow (if, for, while, loop, match)
//! - Jump statements (return, break, continue)
//! - Context and with statements

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::Parser;

impl<'a> Parser<'a> {
    // === Variable Declarations ===

    pub(crate) fn parse_mut_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mut)?;
        self.expect(&TokenKind::Let)?;

        let pattern = self.parse_pattern()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            ty,
            value,
            mutability: Mutability::Mutable,
        }))
    }

    pub(crate) fn parse_let(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Let)?;

        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };

        let pattern = self.parse_pattern()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Let(LetStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            ty,
            value,
            mutability,
        }))
    }

    pub(crate) fn parse_const(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Const)?;

        let name = self.expect_identifier()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expression()?;

        Ok(Node::Const(ConstStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            value,
            visibility: Visibility::Private,
        }))
    }

    pub(crate) fn parse_static(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Static)?;

        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };

        let name = self.expect_identifier()?;

        let ty = if self.check(&TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expression()?;

        Ok(Node::Static(StaticStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            value,
            mutability,
            visibility: Visibility::Private,
        }))
    }

    pub(crate) fn parse_type_alias(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        Ok(Node::TypeAlias(TypeAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            visibility: Visibility::Private,
        }))
    }

    /// Parse standalone unit type: `unit UserId: i64 as uid`
    pub(crate) fn parse_unit(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Unit)?;

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let base_type = self.parse_type()?;
        self.expect(&TokenKind::As)?;
        let suffix = self.expect_identifier()?;

        Ok(Node::Unit(UnitDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            base_type,
            suffix,
            visibility: Visibility::Private,
        }))
    }

    pub(crate) fn parse_extern(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Extern)?;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        Ok(Node::Extern(ExternDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            params,
            return_type,
            visibility: Visibility::Private,
        }))
    }

    // === Control Flow ===

    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        // Check for if-let syntax: if let PATTERN = EXPR:
        let (let_pattern, condition) = if self.check(&TokenKind::Let) {
            self.advance();
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::Assign)?;
            let expr = self.parse_expression()?;
            (Some(pattern), expr)
        } else {
            (None, self.parse_expression()?)
        };

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

        // Check for while-let syntax: while let PATTERN = EXPR:
        let (let_pattern, condition) = if self.check(&TokenKind::Let) {
            self.advance();
            let pattern = self.parse_pattern()?;
            self.expect(&TokenKind::Assign)?;
            let expr = self.parse_expression()?;
            (Some(pattern), expr)
        } else {
            (None, self.parse_expression()?)
        };

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

        let resource = self.parse_expression()?;

        // Optional "as name"
        let name = if self.check(&TokenKind::As) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
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

    // === Jump Statements ===

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

    // === Match ===

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
        let pattern = self.parse_pattern()?;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(&TokenKind::FatArrow)?;

        // Body can be single expression or block
        let body = if self.check(&TokenKind::Newline) {
            self.parse_block()?
        } else {
            let expr = self.parse_expression()?;
            Block {
                span: self.previous.span,
                statements: vec![Node::Expression(expr)],
            }
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

    // === Macro Definition ===

    /// Parse a macro definition: macro name!(params): body
    pub(crate) fn parse_macro_def(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Macro)?;

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Bang)?;

        // Parse macro parameters
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) {
            let param = self.parse_macro_param()?;
            params.push(param);
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;

        self.expect(&TokenKind::Colon)?;

        // Parse macro body as a block
        let body = self.parse_block()?;

        let pattern = MacroPattern {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            params,
            body: MacroBody::Block(body),
        };

        Ok(Node::Macro(MacroDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            patterns: vec![pattern],
            visibility: Visibility::Private,
        }))
    }

    /// Parse a single macro parameter: $name or $name:ty
    pub(crate) fn parse_macro_param(&mut self) -> Result<MacroParam, ParseError> {
        if self.check(&TokenKind::Dollar) {
            self.advance();
            let name = self.expect_identifier()?;
            if self.check(&TokenKind::Colon) {
                self.advance();
                let kind = self.expect_identifier()?;
                match kind.as_str() {
                    "expr" => Ok(MacroParam::Expr(name)),
                    "ty" => Ok(MacroParam::Type(name)),
                    "ident" => Ok(MacroParam::Ident(name)),
                    _ => Ok(MacroParam::Expr(name)), // Default to expr
                }
            } else {
                Ok(MacroParam::Expr(name)) // Default: $x is expression capture
            }
        } else if self.check(&TokenKind::Ellipsis) {
            self.advance();
            if self.check(&TokenKind::Dollar) {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(MacroParam::Variadic {
                    name,
                    separator: None,
                })
            } else {
                Err(ParseError::unexpected_token(
                    "$ after ...",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        } else {
            // Literal token that must match
            let lit = if let TokenKind::Identifier(name) = &self.current.kind {
                let name = name.clone();
                self.advance();
                name
            } else {
                let lexeme = self.current.lexeme.clone();
                self.advance();
                lexeme
            };
            Ok(MacroParam::Literal(lit))
        }
    }
}
