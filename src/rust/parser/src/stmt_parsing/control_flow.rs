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
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Check if this is inline-style (no newline after colon) or block-style
        if !self.check(&TokenKind::Newline) {
            // Inline-style: parse as expression (e.g., `if x < 0: -x else: x`)
            // This returns Node::Expression(Expr::If { ... }) for proper implicit return handling
            let then_expr = self.parse_expression()?;

            // For inline if, we must have an else clause
            if !self.check(&TokenKind::Else) && !self.check(&TokenKind::Elif) {
                return Err(crate::error::ParseError::syntax_error_with_span(
                    "Inline if expression requires an else clause".to_string(),
                    start_span,
                ));
            }

            // Parse elif/else branches as expressions
            let else_branch = if self.check(&TokenKind::Elif) {
                self.advance();
                // Recursively parse as inline if expression
                let elif_expr = self.parse_if_expr_after_condition()?;
                Some(Box::new(elif_expr))
            } else if self.check(&TokenKind::Else) {
                self.advance();
                if self.check(&TokenKind::If) {
                    // else if -> treat as elif
                    self.advance();
                    let elif_expr = self.parse_if_expr_after_condition()?;
                    Some(Box::new(elif_expr))
                } else {
                    self.expect(&TokenKind::Colon)?;
                    Some(Box::new(self.parse_expression()?))
                }
            } else {
                None
            };

            return Ok(Node::Expression(Expr::If {
                let_pattern,
                condition: Box::new(condition),
                then_branch: Box::new(then_expr),
                else_branch,
            }));
        }

        // Block-style: original behavior
        let then_block = self.parse_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let elif_condition = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_block()?;
            elif_branches.push((elif_condition, elif_block));
        }

        // Handle 'else if' as 'elif' (support both syntaxes)
        let mut else_block = None;
        if self.check(&TokenKind::Else) {
            self.advance(); // consume 'else'

            // Check if this is 'else if' (multiple times) or just 'else'
            while self.check(&TokenKind::If) {
                // This is 'else if', treat it as elif
                self.advance(); // consume 'if'
                let elif_condition = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_block()?;
                elif_branches.push((elif_condition, elif_block));

                // Check if there's another 'else if' or final 'else'
                if self.check(&TokenKind::Else) {
                    self.advance(); // consume 'else'
                                    // Loop will check if there's another 'if'
                } else {
                    // No more else/elif, done
                    break;
                }
            }

            // If we're here and consumed an 'else' without following 'if',
            // we need to parse the else block
            if self.check(&TokenKind::Colon) {
                self.expect(&TokenKind::Colon)?;
                else_block = Some(self.parse_block()?);
            }
        }

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
            is_suspend: false,
        }))
    }

    /// Helper for parsing inline if expression after the condition has been parsed
    fn parse_if_expr_after_condition(&mut self) -> Result<Expr, ParseError> {
        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let then_expr = self.parse_expression()?;

        let else_branch = if self.check(&TokenKind::Elif) {
            self.advance();
            Some(Box::new(self.parse_if_expr_after_condition()?))
        } else if self.check(&TokenKind::Else) {
            self.advance();
            if self.check(&TokenKind::If) {
                self.advance();
                Some(Box::new(self.parse_if_expr_after_condition()?))
            } else {
                self.expect(&TokenKind::Colon)?;
                Some(Box::new(self.parse_expression()?))
            }
        } else {
            None
        };

        Ok(Expr::If {
            let_pattern,
            condition: Box::new(condition),
            then_branch: Box::new(then_expr),
            else_branch,
        })
    }

    pub(crate) fn parse_for(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;

        // Check for enumerate shorthand: `for i, item in items:`
        let (pattern, auto_enumerate) = self.parse_for_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;

        // Parse block header (NEWLINE then INDENT)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

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
            is_suspend: false,
            auto_enumerate,
            invariants,
        }))
    }

    /// Parse for loop pattern, detecting enumerate shorthand `for i, item in items:`
    /// Returns (pattern, auto_enumerate)
    fn parse_for_pattern(&mut self) -> Result<(Pattern, bool), ParseError> {
        // Check if this looks like enumerate shorthand: bare `ident, pattern`
        // (not a tuple pattern which uses parentheses)
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            let index_name = name.clone();
            let index_span = self.current.span;
            self.advance();

            // If followed by comma (enumerate shorthand), parse the item pattern
            if self.check(&TokenKind::Comma) {
                self.advance(); // consume comma
                let item_pattern = self.parse_pattern()?;

                // Create tuple pattern for (index, item)
                let tuple_pattern = Pattern::Tuple(vec![Pattern::Identifier(index_name), item_pattern]);
                return Ok((tuple_pattern, true));
            }

            // Not enumerate shorthand - just a regular identifier pattern
            return Ok((Pattern::Identifier(index_name), false));
        }

        // Fall back to standard pattern parsing (handles tuples, wildcards, etc.)
        let pattern = self.parse_pattern()?;
        Ok((pattern, false))
    }

    pub(crate) fn parse_while(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Parse block header (NEWLINE then INDENT)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

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
            is_suspend: false,
            invariants,
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
                let is_primitive = matches!(
                    type_name.as_str(),
                    "i8" | "i16"
                        | "i32"
                        | "i64"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "f32"
                        | "f64"
                        | "bool"
                        | "str"
                        | "nil"
                        | "char"
                );
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

        let body = if self.check(&TokenKind::Arrow)
            || self.check(&TokenKind::FatArrow)
            || self.check(&TokenKind::Colon)
        {
            self.advance();
            // Support inline match arm: `case X => return Y` or `case X: expr`
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                // Parse inline statement (return, expression, etc.)
                let stmt = self.parse_item()?;
                Block {
                    span: self.previous.span,
                    statements: vec![stmt],
                }
            }
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

    // Suspension control flow (async-by-default #45)

    pub(crate) fn parse_if_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::IfSuspend)?;

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

        let mut else_block = None;
        if self.check(&TokenKind::Else) {
            self.advance();
            while self.check(&TokenKind::If) {
                self.advance();
                let elif_condition = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_block()?;
                elif_branches.push((elif_condition, elif_block));

                if self.check(&TokenKind::Else) {
                    self.advance();
                } else {
                    break;
                }
            }

            if self.check(&TokenKind::Colon) {
                self.expect(&TokenKind::Colon)?;
                else_block = Some(self.parse_block()?);
            }
        }

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
            is_suspend: true,
        }))
    }

    pub(crate) fn parse_for_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::ForSuspend)?;

        // Check for enumerate shorthand: `for~ i, item in items:`
        let (pattern, auto_enumerate) = self.parse_for_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;

        // Parse block header (NEWLINE then INDENT)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

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
            is_suspend: true,
            auto_enumerate,
            invariants,
        }))
    }

    pub(crate) fn parse_while_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::WhileSuspend)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Parse block header (NEWLINE then INDENT)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

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
            is_suspend: true,
            invariants,
        }))
    }
}
