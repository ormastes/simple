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
    /// This allows `if cond: x = value` without requiring an else clause.
    /// Also supports member-target chains like `if cond: self.x = value` or
    /// `if cond: dir.field.sub -= 1` by walking [Dot Identifier]* after the head.
    fn is_inline_assignment(&mut self) -> bool {
        // Check if current token is an identifier (or keyword used as variable name)
        // that may begin an assignment lvalue.
        let is_ident_like = matches!(
            self.current.kind,
            TokenKind::Identifier { .. }
                | TokenKind::Self_
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
        if !is_ident_like {
            return false;
        }

        // Fast path: bare `ident =` or `ident OP=`.
        let next = self.peek_next();
        if Self::is_assign_op(&next.kind) {
            return true;
        }
        if !matches!(next.kind, TokenKind::Dot) {
            return false;
        }

        // Member-target lookahead: walk `[Dot Identifier]+` and check for assign at the end.
        // Save parser state so we can restore after the lookahead. We must also push
        // any consumed tokens back to `pending_tokens` because the lexer is stateful
        // and cannot rewind.
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let mut consumed: Vec<crate::token::Token> = Vec::new();

        // Consume head identifier so subsequent peeks step through `.field` chain.
        self.advance();
        consumed.push(self.current.clone());

        let mut found_assign = false;
        loop {
            if !self.check(&TokenKind::Dot) {
                break;
            }
            self.advance(); // consume `.`
            consumed.push(self.current.clone());
            // Expect a member identifier next
            let is_member_ident = matches!(self.current.kind, TokenKind::Identifier { .. });
            if !is_member_ident {
                break;
            }
            self.advance();
            consumed.push(self.current.clone());
            if Self::is_assign_op(&self.current.kind) {
                found_assign = true;
                break;
            }
            // Continue if another `.field` follows; otherwise stop.
            if !self.check(&TokenKind::Dot) {
                break;
            }
        }

        // Restore parser state — push all consumed tokens back to front of pending queue.
        for token in consumed.into_iter().rev() {
            self.pending_tokens.push_front(token);
        }
        self.current = saved_current;
        self.previous = saved_previous;

        found_assign
    }

    /// True if `kind` is `=` or a compound assignment operator.
    fn is_assign_op(kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::Assign
                | TokenKind::PlusAssign
                | TokenKind::MinusAssign
                | TokenKind::StarAssign
                | TokenKind::SlashAssign
                | TokenKind::PercentAssign
        )
    }

    /// Check if inline body is a statement (keyword or assignment) that doesn't require else
    fn is_inline_statement(&mut self) -> bool {
        self.is_inline_statement_keyword() || self.is_inline_assignment()
    }

    /// Parse an `elif`/`else if` body (inline statement or indented block).
    ///
    /// `parse_inline_or_block` now itself reconciles any DEDENT tokens
    /// deferred by this branch's own condition spanning multiple lines via
    /// operator line continuation (e.g. `elif a >\n     b:`) — for both the
    /// inline-statement and indented-block shapes, and for both the "deep"
    /// and "shallow" continuation-column shapes of the indented-block case
    /// (see `parse_condition_block` in `parser_impl/core.rs` and
    /// doc/08_tracking/bug/
    /// seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md).
    /// This wrapper is kept as a named call site for readability/documentation
    /// at each of the four `elif`/`else if` locations below.
    fn parse_elif_or_else_if_body(&mut self) -> Result<Block, ParseError> {
        self.parse_inline_or_block()
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
                    let elif_block = self.parse_elif_or_else_if_body()?;
                    elif_branches.push((elif_pattern, elif_condition, elif_block));
                    if self.check(&TokenKind::Newline)
                        && (self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                            || self.peek_through_newlines_and_indents_is(&TokenKind::Else))
                    {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                }

                let mut else_block = None;
                while self.check(&TokenKind::Else) {
                    self.advance();
                    if self.check(&TokenKind::If) {
                        // else if -> treat as elif
                        self.advance();
                        let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                        self.expect(&TokenKind::Colon)?;
                        let elif_block = self.parse_elif_or_else_if_body()?;
                        elif_branches.push((elif_pattern, elif_condition, elif_block));
                        if self.check(&TokenKind::Newline)
                            && self.peek_through_newlines_and_indents_is(&TokenKind::Else)
                        {
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                        }
                    } else {
                        self.expect(&TokenKind::Colon)?;
                        else_block = Some(self.parse_inline_or_block()?);
                        break;
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
            //
            // The body may also be an ASSIGNMENT (`if cond: d[k] = v`), which
            // `parse_expression` alone rejected with "expected expression,
            // found Assign" even though the block form
            // (`if cond:\n    d[k] = v`) has always worked. An assignment is
            // not an expression, so such an `if` can only be statement-form
            // and is finished by a separate path below.
            let then_node = self.parse_expression_or_assignment()?;
            let then_expr = match then_node {
                Node::Expression(expr) => expr,
                stmt => {
                    return self.finish_inline_statement_if(start_span, let_pattern, condition, stmt);
                }
            };

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

        // Block-style: `parse_condition_block` reconciles any DEDENT tokens
        // deferred by a multi-line condition (e.g., `if expr or\n   expr:`),
        // regardless of whether the compensating DEDENT lands before the
        // block's own Indent (deep continuation) or after the block body
        // (shallow continuation) — see doc/08_tracking/bug/
        // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        let then_block = self.parse_condition_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_elif_or_else_if_body()?;
            elif_branches.push((elif_pattern, elif_condition, elif_block));
            if self.check(&TokenKind::Newline)
                && (self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                    || self.peek_through_newlines_and_indents_is(&TokenKind::Else))
            {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
            }
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
                let elif_block = self.parse_elif_or_else_if_body()?;
                elif_branches.push((elif_pattern, elif_condition, elif_block));

                if self.check(&TokenKind::Newline) && self.peek_through_newlines_and_indents_is(&TokenKind::Else) {
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

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
        self.parse_for_with_label(None)
    }

    pub(crate) fn parse_for_with_label(&mut self, label: Option<String>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;

        // Check for enumerate shorthand: `for i, item in items:`
        let (pattern, auto_enumerate) = self.parse_for_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;

        // Support both block form and inline form:
        // Block: `for x in items:\n    body`
        // Inline: `for x in items: expr`
        if self.check(&TokenKind::Newline) {
            // Parse block header (NEWLINE then INDENT), reconciling any DEDENT
            // tokens deferred by a multi-line `iterable` expression continuation
            // (e.g. `for x in a +\n   b:`) at both candidate points — see
            // doc/08_tracking/bug/
            // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
            self.expect(&TokenKind::Newline)?;
            self.drain_available_deferred_dedents();
            let deferred_before = self.deferred_dedent_count;
            self.deferred_dedent_count = 0;
            // Equal-column shape: skip the Indent expectation when the
            // condition's continuation pseudo-indent level already coincides
            // with the block body's column — see `parse_while_with_label`
            // above for the full rationale.
            let equal_column = self.header_continuation_is_equal_column(deferred_before);
            if !equal_column {
                self.expect(&TokenKind::Indent)?;
            }

            // Parse loop invariants at the start of the block body
            let invariants = self.parse_loop_invariants()?;

            // Parse rest of block body
            let body = self.parse_block_body()?;

            let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
            self.consume_dedents_for_method_chain(deferred);

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
                simd_requested: false,
                is_suspend: false,
                auto_enumerate,
                invariants,
                label,
            }))
        } else {
            // Inline for body: `for x in items: single_statement`
            let stmt = self.parse_item()?;
            let body = Block {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                statements: vec![stmt],
            };
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
                simd_requested: false,
                is_suspend: false,
                auto_enumerate,
                invariants: vec![],
                label,
            }))
        }
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
        self.parse_while_with_label(None)
    }

    pub(crate) fn parse_while_with_label(&mut self, label: Option<String>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        let (body, invariants) = if self.check(&TokenKind::Newline) {
            // Parse block header (NEWLINE then INDENT), reconciling any DEDENT
            // tokens deferred by a multi-line condition expression (e.g.
            // `while expr and\n   expr:`) at both candidate points — the
            // compensating DEDENT can land either immediately here (deep
            // continuation) or only after the whole block body (shallow
            // continuation), alongside the block's own terminating DEDENT.
            // See doc/08_tracking/bug/
            // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
            self.expect(&TokenKind::Newline)?;
            self.drain_available_deferred_dedents();
            let deferred_before = self.deferred_dedent_count;
            self.deferred_dedent_count = 0;
            // Equal-column shape: the condition's continuation pseudo-indent
            // level coincides exactly with the block body's column, so the
            // lexer never emits a fresh Indent here at all (it's already at
            // that level). Detect it and skip straight to body parsing —
            // `parse_block_body` doesn't require Indent to have been
            // physically consumed, it just loops until Dedent.
            let equal_column = self.header_continuation_is_equal_column(deferred_before);
            if !equal_column {
                self.expect(&TokenKind::Indent)?;
            }

            // Parse loop invariants at the start of the block body
            let invariants = self.parse_loop_invariants()?;

            // Parse rest of block body
            let body = self.parse_block_body()?;

            let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
            self.consume_dedents_for_method_chain(deferred);

            (body, invariants)
        } else {
            (self.parse_inline_or_block()?, vec![])
        };

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
            simd_requested: false,
            is_suspend: false,
            invariants,
            label,
        }))
    }

    pub(crate) fn parse_loop(&mut self) -> Result<Node, ParseError> {
        self.parse_loop_with_label(None)
    }

    pub(crate) fn parse_loop_with_label(&mut self, label: Option<String>) -> Result<Node, ParseError> {
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
            simd_requested: false,
            label,
        }))
    }

    /// Parse a labeled loop: `'label: for/while/loop`
    pub(crate) fn parse_labeled_loop(&mut self) -> Result<Node, ParseError> {
        let label = if let TokenKind::Label(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            name
        } else {
            return Err(ParseError::unexpected_token(
                "label",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Expect colon after label
        self.expect(&TokenKind::Colon)?;

        // Parse the loop that follows
        if self.check(&TokenKind::For) {
            self.parse_for_with_label(Some(label))
        } else if self.check(&TokenKind::While) {
            self.parse_while_with_label(Some(label))
        } else if self.check(&TokenKind::Loop) {
            self.parse_loop_with_label(Some(label))
        } else {
            Err(ParseError::unexpected_token(
                "for, while, or loop after label",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    pub(crate) fn parse_context(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        let context = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        // `parse_condition_block` reconciles any DEDENT deferred by a
        // multi-line `context` expression continuation — see
        // doc/08_tracking/bug/seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        let body = self.parse_condition_block()?;

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
        if let Expr::Cast {
            expr,
            target_type: Type::Simple(type_name),
        } = resource.clone()
        {
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

        // Optional "as name"
        let name = if self.check(&TokenKind::As) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            alias_from_cast
        };

        self.expect(&TokenKind::Colon)?;
        // `parse_condition_block` reconciles any DEDENT deferred by a
        // multi-line `resource` expression continuation — see
        // doc/08_tracking/bug/seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        let body = self.parse_condition_block()?;

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
            // Block-style match with indented case arms, reconciling any
            // DEDENT tokens deferred by a multi-line `subject` expression
            // continuation at both candidate points — see doc/08_tracking/
            // bug/seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
            self.advance(); // consume newline
            self.drain_available_deferred_dedents();
            let deferred_before = self.deferred_dedent_count;
            self.deferred_dedent_count = 0;
            // Equal-column shape: the subject's continuation pseudo-indent
            // level coincides exactly with the arms' column, so no fresh
            // Indent appears — skip straight to the arms loop, which does
            // not require Indent to have been physically consumed.
            let equal_column = deferred_before > 0
                && !self.check(&TokenKind::Indent)
                && (self.check(&TokenKind::Case) || self.check(&TokenKind::Pipe));
            if !equal_column {
                self.expect(&TokenKind::Indent)?;
            }

            let mut arms = Vec::new();
            // `=>` inside an arm list is the arm separator, not a TypeScript
            // arrow function -- see is_spurious_match_arm_fat_arrow.
            self.match_arm_depth += 1;
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    break;
                }
                if self.at_enclosing_list_terminator() {
                    break;
                }
                let arm = match self.parse_match_arm() {
                    Ok(arm) => arm,
                    Err(e) => {
                        self.match_arm_depth -= 1;
                        return Err(e);
                    }
                };
                arms.push(arm);
                if !self.consume_match_arm_separator_comma() {
                    break;
                }
            }
            self.match_arm_depth -= 1;

            if self.check(&TokenKind::Dedent) {
                self.advance();
            }

            let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
            self.consume_dedents_for_method_chain(deferred);

            arms
        } else {
            // Inline match: `match self: case X: expr; case Y: expr`
            let mut arms = Vec::new();
            // `=>` inside an arm list is the arm separator, not a TypeScript
            // arrow function -- see is_spurious_match_arm_fat_arrow.
            self.match_arm_depth += 1;
            loop {
                if self.check(&TokenKind::Case) || self.check(&TokenKind::Pipe) {
                    let arm = match self.parse_match_arm() {
                        Ok(arm) => arm,
                        Err(e) => {
                            self.match_arm_depth -= 1;
                            return Err(e);
                        }
                    };
                    arms.push(arm);
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
            self.match_arm_depth -= 1;
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
        // Reconcile any DEDENT deferred by a multi-line `subject` expression
        // continuation at both candidate points — see doc/08_tracking/bug/
        // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        self.expect(&TokenKind::Newline)?;
        self.drain_available_deferred_dedents();
        let deferred_before = self.deferred_dedent_count;
        self.deferred_dedent_count = 0;
        let equal_column = deferred_before > 0
            && !self.check(&TokenKind::Indent)
            && (self.check(&TokenKind::Case) || self.check(&TokenKind::Pipe));
        if !equal_column {
            self.expect(&TokenKind::Indent)?;
        }

        let mut arms = Vec::new();
        self.match_arm_depth += 1;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            if self.at_enclosing_list_terminator() {
                break;
            }
            let arm = match self.parse_match_arm() {
                Ok(arm) => arm,
                Err(e) => {
                    self.match_arm_depth -= 1;
                    return Err(e);
                }
            };
            arms.push(arm);
            if !self.consume_match_arm_separator_comma() {
                break;
            }
        }
        self.match_arm_depth -= 1;

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
        self.consume_dedents_for_method_chain(deferred);

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

    /// Consume the optional `,` that separates two match arms of an INDENTED
    /// (block-style) match body.
    ///
    /// Comma has two distinct roles around a match arm and they never collide:
    ///   * BEFORE the arm's `:`/`=>`/`->` separator it is a multi-pattern
    ///     separator (`case 1, 2, 3:`), consumed inside `parse_pattern`;
    ///   * AFTER the arm's body it separates one arm from the next
    ///     (`0 => 10, 1 => 20`) or trails the last arm (`_ => 0,`).
    /// By the time control returns here the pattern list has already been
    /// consumed, so a comma in this position is unambiguously the second role.
    ///
    /// Without this, every comma-separated / trailing-comma arm list failed
    /// with "expected pattern, found Comma" — the loop re-entered
    /// `parse_match_arm` on the comma itself. That made whole modules
    /// unloadable (e.g. std `tooling/base64_utils.spl`, which had to be
    /// normalised one-arm-per-line as a stopgap). bug doc:
    /// doc/08_tracking/bug/match_arm_comma_separator_rejected_2026-08-02.md
    ///
    /// Only the indented form is affected: the inline form
    /// (`match x: case A: 1; case B: 2`) keeps `;` as its separator, because a
    /// comma there belongs to the enclosing argument / collection list.
    ///
    /// Returns `true` if the arm loop may continue, `false` if the comma was
    /// the ENCLOSING list's separator and must be left unconsumed — see
    /// `at_enclosing_list_terminator` for why `bracket_depth` is the
    /// discriminator.
    pub(crate) fn consume_match_arm_separator_comma(&mut self) -> bool {
        if !self.check(&TokenKind::Comma) {
            return true;
        }
        // A `match` used as a VALUE inside a call's argument list, a
        // struct-literal field list or a collection literal is lexed at
        // bracket depth > 0, and there the comma after the last arm body
        // belongs to that enclosing list, not to the arm list:
        //     Box(a: match x:
        //             1: "one"
        //             _: "other",     <- field separator, NOT an arm separator
        //         b: x)
        // Consuming it made the enclosing parser report
        // "expected comma before argument 'b'", which is why
        // test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl
        // could not be parsed by the seed at all. At statement level
        // (bracket_depth == 0) no enclosing list exists, so the comma is
        // unambiguously an arm separator.
        if self.lexer.bracket_depth > 0 {
            return false;
        }
        self.advance();
        true
    }

    /// True when the current token closes the list that ENCLOSES a `match`
    /// used as a value (`)`, `]`, `}`), i.e. the match's arm list is over.
    ///
    /// The terminator shares the last arm's line, so the lexer has not
    /// flushed a Dedent yet and the arms loop's `Dedent` exit never fires;
    /// without this check the closer was handed to `parse_match_arm`, which
    /// reported "expected pattern, found RParen". Mirrors the self-hosted
    /// `ends_enclosing_list` break in
    /// `src/compiler/10.frontend/core/parser_stmts.spl`
    /// (`parse_match_arms_common`).
    ///
    /// Deliberately NOT gated on `bracket_depth`, unlike the comma case: the
    /// lexer decrements `bracket_depth` as it produces the closer itself, so
    /// by the time the closer is the current token the depth has already
    /// dropped back to the enclosing level (0 for `take_flipped(x, match x:
    /// ... _: "other")`). No gate is needed anyway — a match arm can never
    /// BEGIN with `)`, `]` or `}`, so a closer in pattern position is always
    /// the end of the arm list. At statement level this only changes which
    /// parser reports the stray closer, never whether it is reported.
    pub(crate) fn at_enclosing_list_terminator(&mut self) -> bool {
        self.check(&TokenKind::RParen) || self.check(&TokenKind::RBracket) || self.check(&TokenKind::RBrace)
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

        // A multi-line or-pattern (`case 1 | 2 |\n        3:`) made the lexer
        // open a pseudo-INDENT for the continuation line. Its compensating
        // DEDENT arrives BEFORE the arm body, not after it: the body line is
        // dedented relative to the continuation line, so the stream reads
        // `Newline Dedent Indent <body>`. The old post-body loop below assumed
        // the "shallow" shape only, so the pre-body DEDENT was left in place,
        // `parse_inline_or_block` found a DEDENT where it wanted an INDENT, and
        // the arm loop then tried to read the body's INDENT as the next
        // pattern — reported as `expected pattern, found Indent`.
        //
        // `deferred_dedent_count` is the existing, well-tested reconciliation
        // channel for exactly this (`if`/`while` header continuations, see
        // `parse_condition_block`), and it handles BOTH the deep and shallow
        // shapes. Route the pattern continuation through it instead.
        self.deferred_dedent_count += pattern_indents;

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
        // `parse_condition_block` reconciles any DEDENT deferred by a
        // multi-line condition continuation — see doc/08_tracking/bug/
        // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        let then_block = self.parse_condition_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_condition_block()?;
            elif_branches.push((elif_pattern, elif_condition, elif_block));
        }

        let mut else_block = None;
        if self.check(&TokenKind::Else) {
            self.advance();
            while self.check(&TokenKind::If) {
                self.advance();
                let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
                self.expect(&TokenKind::Colon)?;
                let elif_block = self.parse_condition_block()?;
                elif_branches.push((elif_pattern, elif_condition, elif_block));

                if self.check(&TokenKind::Else) {
                    self.advance();
                } else {
                    break;
                }
            }

            if self.check(&TokenKind::Colon) {
                self.expect(&TokenKind::Colon)?;
                else_block = Some(self.parse_condition_block()?);
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

        // Parse block header (NEWLINE then INDENT), reconciling any DEDENT
        // deferred by a multi-line `iterable` continuation at both candidate
        // points — see doc/08_tracking/bug/
        // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        self.expect(&TokenKind::Newline)?;
        self.drain_available_deferred_dedents();
        let deferred_before = self.deferred_dedent_count;
        self.deferred_dedent_count = 0;
        let equal_column = self.header_continuation_is_equal_column(deferred_before);
        if !equal_column {
            self.expect(&TokenKind::Indent)?;
        }

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

        let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
        self.consume_dedents_for_method_chain(deferred);

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
            simd_requested: false,
            is_suspend: true,
            auto_enumerate,
            invariants,
            label: None,
        }))
    }

    pub(crate) fn parse_while_suspend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::WhileSuspend)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Parse block header (NEWLINE then INDENT), reconciling any DEDENT
        // deferred by a multi-line condition continuation at both candidate
        // points — see doc/08_tracking/bug/
        // seed_elif_while_condition_continuation_indent_ambiguity_2026-07-31.md.
        self.expect(&TokenKind::Newline)?;
        self.drain_available_deferred_dedents();
        let deferred_before = self.deferred_dedent_count;
        self.deferred_dedent_count = 0;
        let equal_column = self.header_continuation_is_equal_column(deferred_before);
        if !equal_column {
            self.expect(&TokenKind::Indent)?;
        }

        // Parse loop invariants at the start of the block body
        let invariants = self.parse_loop_invariants()?;

        // Parse rest of block body
        let body = self.parse_block_body()?;

        let deferred = self.header_continuation_dedents_to_reconcile(deferred_before, equal_column);
        self.consume_dedents_for_method_chain(deferred);

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
            simd_requested: false,
            is_suspend: true,
            invariants,
            label: None,
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

        // Check if this is block form (defer:) or expression/assignment form
        let body = if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            let block = self.parse_block()?;
            DeferBody::Block(block)
        } else {
            // Parse expression, then check for assignment (defer x = value)
            self.parse_defer_body()?
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

    /// Parse an errdefer statement for error-conditional cleanup
    ///
    /// # Syntax
    /// ```simple
    /// errdefer expr             # Single expression
    /// errdefer x = value        # Assignment form
    /// errdefer:                 # Block form
    ///     statements
    /// ```
    ///
    /// Like `defer`, but only runs when the enclosing scope exits with an error.
    pub(crate) fn parse_errdefer(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Errdefer)?;

        // Check if this is block form (errdefer:) or expression/assignment form
        let body = if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            let block = self.parse_block()?;
            DeferBody::Block(block)
        } else {
            // Parse expression, then check for assignment (errdefer x = value)
            self.parse_defer_body()?
        };

        Ok(Node::ErrDefer(ErrDeferStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }

    /// Finish an inline `if` whose then-body is a STATEMENT rather than an
    /// expression — in practice an assignment, e.g. `if cond: d[k] = v`.
    ///
    /// The expression-form path builds a ternary-like `IfExpr`, which cannot
    /// represent an assignment, so this builds a plain statement `IfStmt` with
    /// single-statement blocks instead. An inline `else` is accepted in the
    /// same shape (assignment or expression), and `elif` / `else if` recurse
    /// through the normal `if` parser so chains keep working.
    /// See doc/08_tracking/bug/
    /// parser_inline_if_assignment_body_2026-08-04.md.
    fn finish_inline_statement_if(
        &mut self,
        start_span: Span,
        let_pattern: Option<Pattern>,
        condition: Expr,
        then_stmt: Node,
    ) -> Result<Node, ParseError> {
        let then_block = Block {
            span: self.previous.span,
            statements: vec![then_stmt],
        };

        // Only consume the separating newlines when elif/else actually
        // follows; otherwise they belong to the enclosing block parser.
        if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
            let has_elif_or_else = self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                || self.peek_through_newlines_and_indents_is(&TokenKind::Else);
            if has_elif_or_else {
                while self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                    self.advance();
                }
            }
        }

        let else_block = if self.check(&TokenKind::Elif) {
            // `elif cond: ...` continues the chain as a nested statement if.
            let elif_span = self.current.span;
            self.advance();
            let (elif_pattern, elif_condition) = self.parse_optional_let_pattern()?;
            self.expect(&TokenKind::Colon)?;
            let nested = if self.check(&TokenKind::Newline) {
                let block = self.parse_block()?;
                Node::If(IfStmt {
                    span: elif_span,
                    let_pattern: elif_pattern,
                    condition: elif_condition,
                    then_block: block,
                    elif_branches: Vec::new(),
                    else_block: None,
                    is_suspend: false,
                })
            } else {
                let stmt = self.parse_expression_or_assignment()?;
                self.finish_inline_statement_if(elif_span, elif_pattern, elif_condition, stmt)?
            };
            Some(Block {
                span: self.previous.span,
                statements: vec![nested],
            })
        } else if self.check(&TokenKind::Else) {
            self.advance();
            if self.check(&TokenKind::If) {
                // `else if` — parse_if expects to consume the `if` itself.
                let nested = self.parse_if()?;
                Some(Block {
                    span: self.previous.span,
                    statements: vec![nested],
                })
            } else {
                self.expect(&TokenKind::Colon)?;
                if self.check(&TokenKind::Newline) {
                    Some(self.parse_block()?)
                } else {
                    let stmt = self.parse_expression_or_assignment()?;
                    Some(Block {
                        span: self.previous.span,
                        statements: vec![stmt],
                    })
                }
            }
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
            elif_branches: Vec::new(),
            else_block,
            is_suspend: false,
        }))
    }

    /// Parse defer/errdefer body: either a plain expression or an assignment.
    /// Handles `defer expr` and `defer target = value` uniformly.
    /// Assignment form is wrapped as a single-statement Block.
    ///
    /// B4-sugar Phase 3 (2026-04-25): single-line `defer x.bits[lo..hi] = v`
    /// now runs the same bitfield write desugar that
    /// `parse_expression_or_assignment` applies for top-level statements.
    /// Previously this path constructed an `AssignmentStmt` directly and
    /// bypassed the rewrite, leaving `Index { receiver: FieldAccess
    /// { field: "bits" }, ... }` in the AST — which downstream lowering
    /// cannot handle. The block form `defer:\n    x.bits[…] = v` already
    /// worked because `parse_block` dispatches through
    /// `parse_expression_or_assignment`.
    fn parse_defer_body(&mut self) -> Result<DeferBody, ParseError> {
        let expr = self.parse_expression()?;

        // Check for assignment: defer/errdefer target = value
        if self.check(&TokenKind::Assign) {
            let assign_span = self.current.span;
            self.advance(); // consume '='
            let value = self.parse_expression()?;

            // B4-sugar Phase 3: desugar `defer x.bits[lo..hi] = v` here too.
            // Side-effect guard mirrors the no_paren wrapper.
            let (target, value) =
                if let Some((lvalue, lo, hi)) = crate::expressions::bitfield::match_bits_write_target(&expr) {
                    if !crate::expressions::bitfield::is_pure_lvalue(&lvalue) {
                        return Err(ParseError::syntax_error_with_span(
                            "bitfield assignment with side-effecting receiver/index \
                         in defer body — bind to a temp first. The desugar \
                         duplicates the lvalue, so calls on the lvalue spine \
                         would re-execute their side effects.",
                            assign_span,
                        ));
                    }
                    let new_value = crate::expressions::bitfield::build_bits_write_value(lvalue.clone(), lo, hi, value);
                    (lvalue, new_value)
                } else {
                    (expr, value)
                };

            // Wrap as a Block containing one assignment Node
            let assign_node = Node::Assignment(AssignmentStmt {
                span: assign_span,
                target,
                op: AssignOp::Assign,
                value,
            });
            Ok(DeferBody::Block(Block {
                span: assign_span,
                statements: vec![assign_node],
            }))
        } else {
            Ok(DeferBody::Expr(expr))
        }
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
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            then_body.push(self.parse_item()?);
        }
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        // Check for else branch
        // Skip newlines between dedent and else
        while self.check(&TokenKind::Newline) {
            self.advance();
        }
        let else_body = if self.check(&TokenKind::Else) {
            self.advance(); // consume 'else'
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;
            let mut else_items = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    break;
                }
                else_items.push(self.parse_item()?);
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
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
