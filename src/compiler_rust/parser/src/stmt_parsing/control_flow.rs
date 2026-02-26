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
    /// Check if current token is an inline statement keyword (return, break, continue)
    fn is_inline_statement_keyword(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Return | TokenKind::Break | TokenKind::Continue
        )
    }

    /// Check if the inline body looks like an assignment statement (identifier = expr)
    /// This allows `if cond: x = value` without requiring an else clause
    fn is_inline_assignment(&mut self) -> bool {
        // Check if current token is an identifier (or keyword used as variable name) followed by =
        let is_ident_like = matches!(
            self.current.kind,
            TokenKind::Identifier { .. }
            | TokenKind::Result
            | TokenKind::Type
            | TokenKind::Default
            | TokenKind::Val
            | TokenKind::Var
            | TokenKind::New
            | TokenKind::Old
            | TokenKind::From
            | TokenKind::To
            | TokenKind::In
            | TokenKind::Is
            | TokenKind::As
            | TokenKind::Match
            | TokenKind::Use
            | TokenKind::Out
            | TokenKind::OutErr
            | TokenKind::Gen
            | TokenKind::Impl
            | TokenKind::Exists
            | TokenKind::Context
            | TokenKind::Alias
            | TokenKind::Bounds
        );
        if is_ident_like {
            // Peek ahead to see if next token is = or compound assignment
            let next = self.peek_next();
            return matches!(
                next.kind,
                TokenKind::Assign
                    | TokenKind::PlusAssign
                    | TokenKind::MinusAssign
                    | TokenKind::StarAssign
                    | TokenKind::SlashAssign
                    | TokenKind::PercentAssign
            );
        }
        false
    }

    /// Check if inline body is a statement (keyword or assignment) that doesn't require else
    fn is_inline_statement(&mut self) -> bool {
        self.is_inline_statement_keyword() || self.is_inline_assignment()
    }

    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        // Accept ':' or 'then' keyword before the if body
        if self.check(&TokenKind::Then) {
            self.advance(); // consume 'then'
        } else {
            self.expect(&TokenKind::Colon)?;
        }

        // Check if this is inline-style (no newline after colon) or block-style
        if !self.check(&TokenKind::Newline) {
            // Check if this is an inline statement (return, break, continue, assignment)
            // These don't require an else clause since they're control flow statements
            if self.is_inline_statement() {
                // Parse inline statement like match_arm does
                let stmt = self.parse_item()?;
                let then_block = Block {
                    span: self.previous.span,
                    statements: vec![stmt],
                };

                // Parse optional elif/else as blocks
                // Peek through newlines to check for elif/else continuation
                // (e.g., `if cond: x = value\nelse: y = other`)
                // Only consume newlines if elif/else actually follows,
                // otherwise leave them for the outer block parser.
                if self.check(&TokenKind::Newline) {
                    let has_elif_or_else = self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                        || self.peek_through_newlines_and_indents_is(&TokenKind::Else);
                    if has_elif_or_else {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                }

                let mut elif_branches = Vec::new();
                while self.check(&TokenKind::Elif) {
                    self.advance();
                    let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                    self.expect(&TokenKind::Colon)?;
                    let elif_block = self.parse_inline_or_block()?;
                    elif_branches.push((elif_pattern, elif_condition, elif_block));
                }

                let mut else_block = None;
                if self.check(&TokenKind::Else) {
                    self.advance();
                    if self.check(&TokenKind::If) {
                        // else if -> treat as elif
                        self.advance();
                        let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                        self.expect(&TokenKind::Colon)?;
                        let elif_block = self.parse_inline_or_block()?;
                        elif_branches.push((elif_pattern, elif_condition, elif_block));
                    } else {
                        self.expect(&TokenKind::Colon)?;
                        else_block = Some(self.parse_inline_or_block()?);
                    }
                }

                return Ok(Node::If(IfStmt {
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
                }));
            }

            // Inline-style: could be expression (if x < 0: -x else: x)
            // or statement (if cond: func_call())
            // Parse the body first, then check if else follows
            let then_expr = self.parse_expression()?;

            // Peek through newlines/dedents to check for elif/else continuation.
            // Only consume newlines if elif/else actually follows,
            // otherwise leave them for the outer block parser.
            if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                let has_elif_or_else = self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                    || self.peek_through_newlines_and_indents_is(&TokenKind::Else);
                if has_elif_or_else {
                    while self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                }
            }

            // If no else clause, treat as statement-form (no else required)
            if !self.check(&TokenKind::Else) && !self.check(&TokenKind::Elif) {
                let then_block = Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(then_expr)],
                };
                return Ok(Node::If(IfStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    let_pattern,
                    condition,
                    then_block,
                    elif_branches: Vec::new(),
                    else_block: None,
                    is_suspend: false,
                }));
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
                    if self.check(&TokenKind::Newline) {
                        // Block-form else: parse as DoBlock
                        self.advance(); // consume Newline
                        self.expect(&TokenKind::Indent)?;
                        let mut stmts = Vec::new();
                        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                                break;
                            }
                            stmts.push(self.parse_item()?);
                            if self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                        }
                        if self.check(&TokenKind::Dedent) {
                            self.advance();
                        }
                        Some(Box::new(Expr::DoBlock(stmts)))
                    } else {
                        Some(Box::new(self.parse_expression()?))
                    }
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

        // Save deferred dedent count before parsing block.
        // Multi-line conditions (e.g., `if expr or\n   expr:`) may have consumed
        // Indent tokens during expression parsing whose matching Dedents appear after
        // the block body. These are tracked in `deferred_dedent_count`.
        let deferred_before = self.deferred_dedent_count;
        self.deferred_dedent_count = 0;

        // Block-style: original behavior
        let then_block = self.parse_block()?;

        // Consume deferred Dedent tokens from multi-line expression continuation.
        let deferred = self.deferred_dedent_count + deferred_before;
        self.deferred_dedent_count = 0;
        for _ in 0..deferred {
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_inline_or_block()?;
            elif_branches.push((elif_pattern, elif_condition, elif_block));
        }

        // Handle 'else if' as 'elif' (support both syntaxes)
        let mut else_block = None;
        if self.check(&TokenKind::Else) {
            self.advance(); // consume 'else'

            // Check if this is 'else if' (multiple times) or just 'else'
            while self.check(&TokenKind::If) {
                // This is 'else if', treat it as elif
                self.advance(); // consume 'if'
                let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_inline_or_block()?;
                elif_branches.push((elif_pattern, elif_condition, elif_block));

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
                else_block = Some(self.parse_inline_or_block()?);
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

        // Skip newlines before checking for else/elif (allows multi-line inline if)
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

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

        let arms = if self.check(&TokenKind::Newline) {
            // Block-style match with indented case arms
            self.advance(); // consume newline
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
            arms
        } else {
            // Inline match: `match self: case X: expr; case Y: expr`
            let mut arms = Vec::new();
            loop {
                if self.check(&TokenKind::Case) || self.check(&TokenKind::Pipe) {
                    arms.push(self.parse_match_arm()?);
                } else {
                    break;
                }
                // Consume semicolons between inline arms
                if self.check(&TokenKind::Semicolon) {
                    self.advance();
                } else {
                    break;
                }
            }
            arms
        };

        Ok(Node::Match(MatchStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            subject,
            arms,
            is_suspend: false,
        }))
    }

    pub(crate) fn parse_match_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::MatchSuspend)?;

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
            is_suspend: true,
        }))
    }

    pub(crate) fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;

        // Support both syntaxes:
        // - `case pattern:` or `case pattern ->`  (traditional)
        // - `| pattern ->`  (Erlang-style, preferred)
        let is_pipe_syntax = self.check(&TokenKind::Pipe);
        if is_pipe_syntax {
            self.advance(); // consume `|`
        } else if self.check(&TokenKind::Case) {
            self.advance();
        }

        // Reset pattern indent count before parsing pattern
        self.pattern_indent_count = 0;
        let pattern = self.parse_pattern()?;

        // Save the count of INDENTs consumed during pattern parsing
        // (for multi-line or-patterns like `case 1 | 2\n   | 3:`)
        let pattern_indents = self.pattern_indent_count;
        self.pattern_indent_count = 0;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // For `| pattern ->` syntax, only accept `->`
        // For `case pattern:` syntax, accept `->`, `=>`, or `:`
        let valid_separator = if is_pipe_syntax {
            self.check(&TokenKind::Arrow)
        } else {
            self.check(&TokenKind::Arrow) || self.check(&TokenKind::FatArrow) || self.check(&TokenKind::Colon)
        };

        let body = if valid_separator {
            self.advance();
            self.parse_inline_or_block()?
        } else {
            let expected = if is_pipe_syntax { "->" } else { "-> or => or :" };
            return Err(ParseError::unexpected_token(
                expected,
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Consume DEDENTs that balance the INDENTs consumed during multi-line pattern parsing
        // These DEDENTs appear AFTER the arm body in the token stream
        for _ in 0..pattern_indents {
            // Skip any newlines before the DEDENT
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }

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
            let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_block()?;
            elif_branches.push((elif_pattern, elif_condition, elif_block));
        }

        let mut else_block = None;
        if self.check(&TokenKind::Else) {
            self.advance();
            while self.check(&TokenKind::If) {
                self.advance();
                let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_block()?;
                elif_branches.push((elif_pattern, elif_condition, elif_block));

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

    /// Parse a defer statement for scope-based cleanup
    ///
    /// # Syntax
    /// ```simple
    /// defer expr             # Single expression
    /// defer:                 # Block form
    ///     statements
    /// ```
    pub(crate) fn parse_defer(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Defer)?;

        // Check if this is block form (defer:) or expression form (defer expr)
        let body = if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            let block = self.parse_block()?;
            DeferBody::Block(block)
        } else {
            // Parse single expression
            let expr = self.parse_expression()?;
            DeferBody::Expr(expr)
        };

        Ok(Node::Defer(DeferStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }

    /// Parse `when COND: ... else: ...` conditional compilation block.
    /// Desugars to an if/else at the module level.
    /// The caller has already verified the `when` identifier is present.
    pub(crate) fn parse_when_block(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'when' identifier

        // Parse the condition expression
        let condition = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;

        // Parse the 'then' body - this is a block of items (not statements)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let mut then_body = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) { self.advance(); }
            if self.check(&TokenKind::Dedent) { break; }
            then_body.push(self.parse_item()?);
        }
        if self.check(&TokenKind::Dedent) { self.advance(); }

        // Check for else branch
        // Skip newlines between dedent and else
        while self.check(&TokenKind::Newline) { self.advance(); }
        let else_body = if self.check(&TokenKind::Else) {
            self.advance(); // consume 'else'
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;
            let mut else_items = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) { self.advance(); }
                if self.check(&TokenKind::Dedent) { break; }
                else_items.push(self.parse_item()?);
            }
            if self.check(&TokenKind::Dedent) { self.advance(); }
            Some(else_items)
        } else {
            None
        };

        // Desugar: emit the items from whichever branch is selected.
        // For now, always emit the 'else' branch (or then if no else).
        // The condition is preserved for downstream compile-time evaluation.
        // We use IfStmt as a container since the AST already supports it.
        let body_nodes = if let Some(else_items) = else_body {
            // Emit both branches - downstream will evaluate the condition
            let mut all_items = then_body;
            all_items.extend(else_items);
            all_items
        } else {
            then_body
        };

        // Push all items as pending statements and return the first
        if body_nodes.is_empty() {
            Ok(Node::Pass(PassStmt { span: start_span }))
        } else {
            let mut items = body_nodes.into_iter();
            let first = items.next().unwrap();
            for item in items {
                self.pending_statements.push(item);
            }
            Ok(first)
        }
    }
}
