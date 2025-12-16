//! Expression parsing module
//!
//! This module contains all expression parsing logic for the Simple language parser.
//! It implements a Pratt parser (precedence climbing) for binary operators.

use crate::ast::*;
use crate::error::ParseError;
use crate::parser::ParserMode;
use crate::token::{FStringToken, TokenKind};

use super::Parser;

/// Macro to generate binary operator parsing functions.
/// Reduces duplication in precedence-climbing parser.
macro_rules! parse_binary_single {
    ($fn_name:ident, $next_fn:ident, $token:ident, $op:expr) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            while self.check(&TokenKind::$token) {
                self.advance();
                let right = self.$next_fn()?;
                left = Expr::Binary {
                    op: $op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
            Ok(left)
        }
    };
}

/// Macro for binary operators with multiple token options
macro_rules! parse_binary_multi {
    ($fn_name:ident, $next_fn:ident, $( $token:ident => $op:expr ),+ $(,)?) => {
        pub(crate) fn $fn_name(&mut self) -> Result<Expr, ParseError> {
            let mut left = self.$next_fn()?;
            loop {
                let op = match &self.current.kind {
                    $( TokenKind::$token => $op, )+
                    _ => break,
                };
                self.advance();
                let right = self.$next_fn()?;
                left = Expr::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                };
            }
            Ok(left)
        }
    };
}

impl<'a> Parser<'a> {
    /// Helper to convert an expression + args into a Call or MethodCall.
    /// If expr is FieldAccess, create MethodCall; otherwise create Call.
    fn make_call_expr(&self, expr: Expr, args: Vec<Argument>) -> Expr {
        match expr {
            Expr::FieldAccess { receiver, field } => Expr::MethodCall {
                receiver,
                method: field,
                args,
            },
            _ => Expr::Call {
                callee: Box::new(expr),
                args,
            },
        }
    }

    /// Helper to create a Slice expression
    fn make_slice_expr(&self, receiver: Expr, start: Option<Expr>, end: Option<Expr>, step: Option<Box<Expr>>) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }

    // === Expression Parsing (Pratt Parser) ===

    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_or()
    }

    /// Parse optional step expression for slice syntax (`:step` at end of slice)
    fn parse_optional_step(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::Colon) {
            self.advance();
            if self.check(&TokenKind::RBracket) {
                Ok(None)
            } else {
                Ok(Some(Box::new(self.parse_expression()?)))
            }
        } else {
            Ok(None)
        }
    }

    /// Parse optional expression before RBracket
    fn parse_optional_expr_before_bracket(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::RBracket) {
            Ok(None)
        } else {
            Ok(Some(Box::new(self.parse_expression()?)))
        }
    }

    pub(crate) fn parse_expression_or_assignment(&mut self) -> Result<Node, ParseError> {
        let expr = self.parse_expression()?;

        // Check for assignment
        let assign_op = match &self.current.kind {
            TokenKind::Assign => Some(AssignOp::Assign),
            TokenKind::PlusAssign => Some(AssignOp::AddAssign),
            TokenKind::MinusAssign => Some(AssignOp::SubAssign),
            TokenKind::StarAssign => Some(AssignOp::MulAssign),
            TokenKind::SlashAssign => Some(AssignOp::DivAssign),
            _ => None,
        };

        if let Some(op) = assign_op {
            let span = self.current.span;
            self.advance();
            let value = self.parse_expression()?;
            Ok(Node::Assignment(AssignmentStmt {
                span,
                target: expr,
                op,
                value,
            }))
        } else {
            // Parse the expression with potential no-paren calls
            let expr = self.parse_with_no_paren_calls(expr)?;

            // Check for infix keywords (to, not_to) and convert to method calls
            // e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
            let expr = self.parse_infix_keywords(expr)?;

            Ok(Node::Expression(expr))
        }
    }

    /// Parse no-paren calls on an expression
    fn parse_with_no_paren_calls(&mut self, expr: Expr) -> Result<Expr, ParseError> {
        // Check for colon-block on plain identifier FIRST
        // e.g., `given:` or `describe:` without arguments
        // This must come before can_start_argument() check because colon is in that list
        if self.is_callable_expr(&expr) && self.is_at_colon_block() {
            if let Some(block_lambda) = self.try_parse_colon_block()? {
                let args = vec![Argument {
                    name: None,
                    value: block_lambda,
                }];
                return Ok(self.make_call_expr(expr, args));
            }
        }
        // Check for no-parentheses call at statement level
        // Only for identifiers or field access followed by argument-starting tokens
        else if self.is_callable_expr(&expr) && self.can_start_argument() {
            // In strict mode, only allow outermost no-paren call
            // If we're already inside a no-paren call (depth > 0), require parentheses
            if self.mode == ParserMode::Strict && self.no_paren_depth > 0 {
                return Ok(expr);
            }

            // Track depth for strict mode
            self.no_paren_depth += 1;
            let mut args = self.parse_no_paren_arguments()?;
            self.no_paren_depth -= 1;

            // Check for trailing lambda: func arg \x: body
            if self.check(&TokenKind::Backslash) {
                let trailing_lambda = self.parse_trailing_lambda()?;
                args.push(Argument {
                    name: None,
                    value: trailing_lambda,
                });
            }
            // Check for trailing colon-block: func arg:
            //     body
            // This becomes: func(arg, fn(): body)
            else if self.check(&TokenKind::Colon) {
                if let Some(block_lambda) = self.try_parse_colon_block()? {
                    args.push(Argument {
                        name: None,
                        value: block_lambda,
                    });
                }
            }

            if !args.is_empty() {
                return Ok(self.make_call_expr(expr, args));
            }
        }
        Ok(expr)
    }

    /// Parse infix keywords (to, not_to) as method calls
    /// e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
    fn parse_infix_keywords(&mut self, mut expr: Expr) -> Result<Expr, ParseError> {
        loop {
            let method_name = match &self.current.kind {
                TokenKind::To => "to",
                TokenKind::NotTo => "not_to",
                _ => break,
            };

            self.advance(); // consume `to` or `not_to`

            // Parse the argument expression (with no-paren calls allowed)
            let arg_expr = self.parse_expression()?;
            let arg_expr = self.parse_with_no_paren_calls(arg_expr)?;

            // Convert to method call: expr.to(arg) or expr.not_to(arg)
            expr = Expr::MethodCall {
                receiver: Box::new(expr),
                method: method_name.to_string(),
                args: vec![Argument {
                    name: None,
                    value: arg_expr,
                }],
            };
        }
        Ok(expr)
    }

    /// Check if an expression can be a callee for no-parens calls
    fn is_callable_expr(&self, expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::Identifier(_) | Expr::FieldAccess { .. } | Expr::Path(_)
        )
    }

    /// Check if we're at a colon-block pattern: `:` followed by newline and indent
    /// This is used to distinguish `func:` blocks from `func name: value` named args
    fn is_at_colon_block(&mut self) -> bool {
        if !self.check(&TokenKind::Colon) {
            return false;
        }

        // Peek ahead to see if there's a newline after the colon
        self.peek_is(&TokenKind::Newline)
    }

    /// Check if current token can start an argument (for no-parens calls)
    fn can_start_argument(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Integer(_)
                | TokenKind::TypedInteger(_, _)
                | TokenKind::Float(_)
                | TokenKind::TypedFloat(_, _)
                | TokenKind::String(_)
                | TokenKind::RawString(_)
                | TokenKind::TypedString(_, _)
                | TokenKind::TypedRawString(_, _)
                | TokenKind::FString(_)
                | TokenKind::Bool(_)
                | TokenKind::Nil
                | TokenKind::Symbol(_)
                | TokenKind::Identifier(_)
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
                | TokenKind::Backslash
                | TokenKind::Colon // for named args like name: "value"
        )
    }

    /// Parse arguments without parentheses.
    /// - Normal mode: comma-separated (required)
    /// - Strict mode: commas optional, space-separated allowed
    fn parse_no_paren_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        let mut args = Vec::new();

        // Parse first argument
        if let Ok(arg) = self.parse_single_argument() {
            args.push(arg);
        } else {
            return Ok(args);
        }

        // Parse remaining arguments
        loop {
            // Check for comma (required in normal mode, optional in strict mode)
            let has_comma = self.check(&TokenKind::Comma);
            if has_comma {
                self.advance(); // consume comma
            }

            // In strict mode, continue parsing if we can start another argument
            // In normal mode, require comma to continue
            if self.mode == ParserMode::Strict {
                // Strict mode: commas optional, continue if can start argument
                if !self.can_start_argument() {
                    break;
                }
            } else {
                // Normal mode: require comma to continue
                if !has_comma {
                    break;
                }
            }

            // Parse next argument
            if let Ok(arg) = self.parse_single_argument() {
                args.push(arg);
            } else {
                break;
            }
        }

        Ok(args)
    }

    /// Parse a single argument (possibly named)
    fn parse_single_argument(&mut self) -> Result<Argument, ParseError> {
        // Check for named argument: name: value
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name_clone = name.clone();
            // Peek ahead to check for colon
            if self.peek_is(&TokenKind::Colon) {
                self.advance(); // consume identifier
                self.advance(); // consume colon
                // In strict mode, track depth when parsing named argument value
                let prev_depth = self.no_paren_depth;
                if self.mode == ParserMode::Strict {
                    self.no_paren_depth += 1;
                }
                let value = self.parse_expression()?;
                self.no_paren_depth = prev_depth;
                return Ok(Argument {
                    name: Some(name_clone),
                    value,
                });
            }
        }
        // Positional argument
        // In strict mode, track depth when parsing argument value
        let prev_depth = self.no_paren_depth;
        if self.mode == ParserMode::Strict {
            self.no_paren_depth += 1;
        }
        let value = self.parse_expression()?;
        self.no_paren_depth = prev_depth;
        Ok(Argument { name: None, value })
    }

    // Binary expression parsing with precedence (using macros to reduce duplication)
    // Precedence (lowest to highest): or, and, equality, comparison, bitwise_or, bitwise_xor, bitwise_and, shift, term, factor, power

    // Single-token operators
    parse_binary_single!(parse_or, parse_and, Or, BinOp::Or);
    parse_binary_single!(parse_and, parse_equality, And, BinOp::And);
    parse_binary_single!(parse_bitwise_or, parse_bitwise_xor, Pipe, BinOp::BitOr);
    parse_binary_single!(parse_bitwise_xor, parse_bitwise_and, Caret, BinOp::BitXor);
    parse_binary_single!(parse_bitwise_and, parse_shift, Ampersand, BinOp::BitAnd);

    // Multi-token operators
    parse_binary_multi!(parse_equality, parse_comparison,
        Eq => BinOp::Eq,
        NotEq => BinOp::NotEq,
        Is => BinOp::Is,
        In => BinOp::In,
    );

    /// Parse comparisons with chaining support: a < b < c becomes (a < b) and (b < c)
    pub(crate) fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_bitwise_or()?;

        // Check if there's a comparison operator
        let op = match &self.current.kind {
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::LtEq => Some(BinOp::LtEq),
            TokenKind::GtEq => Some(BinOp::GtEq),
            _ => None,
        };

        if op.is_none() {
            return Ok(left);
        }

        // We have at least one comparison
        let mut comparisons: Vec<Expr> = Vec::new();
        let mut prev_right = left;

        loop {
            let op = match &self.current.kind {
                TokenKind::Lt => BinOp::Lt,
                TokenKind::Gt => BinOp::Gt,
                TokenKind::LtEq => BinOp::LtEq,
                TokenKind::GtEq => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_bitwise_or()?;

            comparisons.push(Expr::Binary {
                op,
                left: Box::new(prev_right.clone()),
                right: Box::new(right.clone()),
            });

            prev_right = right;
        }

        // If only one comparison, return it directly
        if comparisons.len() == 1 {
            return Ok(comparisons.into_iter().next().unwrap());
        }

        // Chain multiple comparisons with 'and'
        let mut result = comparisons.remove(0);
        for cmp in comparisons {
            result = Expr::Binary {
                op: BinOp::And,
                left: Box::new(result),
                right: Box::new(cmp),
            };
        }

        Ok(result)
    }

    parse_binary_multi!(parse_shift, parse_term,
        ShiftLeft => BinOp::ShiftLeft,
        ShiftRight => BinOp::ShiftRight,
    );

    parse_binary_multi!(parse_term, parse_factor,
        Plus => BinOp::Add,
        Minus => BinOp::Sub,
    );

    parse_binary_multi!(parse_factor, parse_power,
        Star => BinOp::Mul,
        Slash => BinOp::Div,
        Percent => BinOp::Mod,
        DoubleSlash => BinOp::FloorDiv,
    );

    pub(crate) fn parse_power(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_unary()?;

        if self.check(&TokenKind::DoubleStar) {
            self.advance();
            let right = self.parse_power()?; // Right associative
            return Ok(Expr::Binary {
                op: BinOp::Pow,
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    pub(crate) fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Minus => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Not => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Tilde => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::BitNot,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Ampersand => {
                self.advance();
                // Check for &mut expr (mutable borrow)
                if self.check(&TokenKind::Mut) {
                    self.advance();
                    let operand = self.parse_unary()?;
                    Ok(Expr::Unary {
                        op: UnaryOp::RefMut,
                        operand: Box::new(operand),
                    })
                } else {
                    let operand = self.parse_unary()?;
                    Ok(Expr::Unary {
                        op: UnaryOp::Ref,
                        operand: Box::new(operand),
                    })
                }
            }
            TokenKind::Star => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Deref,
                    operand: Box::new(operand),
                })
            }
            TokenKind::Await => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Await(Box::new(operand)))
            }
            TokenKind::Yield => {
                self.advance();
                // yield can be bare (yield) or with value (yield expr)
                if self.is_at_end()
                    || matches!(
                        self.current.kind,
                        TokenKind::Newline
                            | TokenKind::Dedent
                            | TokenKind::RParen
                            | TokenKind::RBrace
                            | TokenKind::Comma
                    )
                {
                    Ok(Expr::Yield(None))
                } else {
                    let operand = self.parse_unary()?;
                    Ok(Expr::Yield(Some(Box::new(operand))))
                }
            }
            _ => self.parse_postfix(),
        }
    }

    pub(crate) fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            match &self.current.kind {
                TokenKind::LParen => {
                    expr = self.parse_call(expr)?;
                }
                TokenKind::Bang => {
                    // Macro invocation: name!(args)
                    if let Expr::Identifier(name) = expr {
                        self.advance(); // consume !
                        let args = self.parse_macro_args()?;
                        expr = Expr::MacroInvocation { name, args };
                    } else {
                        break;
                    }
                }
                TokenKind::LBracket => {
                    self.advance();

                    // Check for slicing: arr[start:end:step] or arr[:] or arr[::step]
                    // Note: :: is lexed as DoubleColon, so we need to handle both Colon and DoubleColon
                    if self.check(&TokenKind::DoubleColon) {
                        // Slice starting with :: (no start, no end)
                        self.advance();
                        let step = self.parse_optional_expr_before_bracket()?;
                        self.expect(&TokenKind::RBracket)?;
                        expr = self.make_slice_expr(expr, None, None, step);
                    } else if self.check(&TokenKind::Colon) {
                        // Slice starting with : (no start)
                        self.advance();
                        // Check for ::step (no end)
                        if self.check(&TokenKind::Colon) {
                            self.advance();
                            let step = self.parse_optional_expr_before_bracket()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = self.make_slice_expr(expr, None, None, step);
                        } else {
                            let end = self.parse_optional_expr_before_bracket()?;
                            let step = self.parse_optional_step()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: None,
                                end,
                                step,
                            };
                        }
                    } else {
                        // Parse first expression (could be index or slice start)
                        let first = self.parse_expression()?;

                        if self.check(&TokenKind::DoubleColon) {
                            // Slice with start::step (no end)
                            self.advance();
                            let step = self.parse_optional_expr_before_bracket()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: Some(Box::new(first)),
                                end: None,
                                step,
                            };
                        } else if self.check(&TokenKind::Colon) {
                            // It's a slice
                            self.advance();
                            let end = if self.check(&TokenKind::Colon)
                                || self.check(&TokenKind::RBracket)
                            {
                                None
                            } else {
                                Some(Box::new(self.parse_expression()?))
                            };
                            let step = self.parse_optional_step()?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: Some(Box::new(first)),
                                end,
                                step,
                            };
                        } else {
                            // Regular index access
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Index {
                                receiver: Box::new(expr),
                                index: Box::new(first),
                            };
                        }
                    }
                }
                TokenKind::Dot => {
                    self.advance();
                    // Support tuple element access: tuple.0, tuple.1
                    if let TokenKind::Integer(n) = &self.current.kind {
                        let index = *n;
                        self.advance();
                        expr = Expr::TupleIndex {
                            receiver: Box::new(expr),
                            index: index as usize,
                        };
                    } else {
                        let field = self.expect_method_name()?;
                        if self.check(&TokenKind::LParen) {
                            let mut args = self.parse_arguments()?;
                            // Check for trailing block: obj.method(args) \x: body
                            if self.check(&TokenKind::Backslash) {
                                let trailing_lambda = self.parse_trailing_lambda()?;
                                args.push(Argument {
                                    name: None,
                                    value: trailing_lambda,
                                });
                            }
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args,
                            };
                        } else if self.check(&TokenKind::Backslash) {
                            // Method call with only trailing block: obj.method \x: body
                            let trailing_lambda = self.parse_trailing_lambda()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument {
                                    name: None,
                                    value: trailing_lambda,
                                }],
                            };
                        } else {
                            expr = Expr::FieldAccess {
                                receiver: Box::new(expr),
                                field,
                            };
                        }
                    }
                }
                TokenKind::Arrow => {
                    // Functional update operator: obj->method(args)
                    // Desugars to: obj = obj.method(args)
                    self.advance();
                    let method = self.expect_method_name()?;
                    let args = self.parse_arguments()?;
                    expr = Expr::FunctionalUpdate {
                        target: Box::new(expr),
                        method,
                        args,
                    };
                }
                TokenKind::Question => {
                    // Try operator: expr? - unwrap Ok or early return Err
                    self.advance();
                    expr = Expr::Try(Box::new(expr));
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    pub(crate) fn parse_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mut args = self.parse_arguments()?;
        // Check for trailing block: func(args) \x: body
        if self.check(&TokenKind::Backslash) {
            let trailing_lambda = self.parse_trailing_lambda()?;
            args.push(Argument {
                name: None,
                value: trailing_lambda,
            });
        }
        // Note: Colon-block syntax like func(args): body is only supported in the
        // no-paren call context (parse_expression_or_assignment), not here.
        // This avoids conflicts with for/while/if statements that use colon after expressions.
        Ok(Expr::Call {
            callee: Box::new(callee),
            args,
        })
    }

    /// Parse a trailing block lambda: \params: body
    pub(crate) fn parse_trailing_lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::Backslash)?;
        let params = self.parse_lambda_params()?;
        self.expect(&TokenKind::Colon)?;

        // Check if body is an indented block or inline expression
        let body = if self.check(&TokenKind::Newline) {
            // Peek ahead to see if we have a newline + indent (block body)
            if self.peek_is(&TokenKind::Indent) {
                // Parse as block
                let block = self.parse_block()?;
                Expr::DoBlock(block.statements)
            } else {
                // Just a newline, parse next expression
                self.parse_expression()?
            }
        } else {
            // Inline expression
            self.parse_expression()?
        };

        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode: MoveMode::Copy,
        })
    }

    /// Parse lambda parameters (comma-separated identifiers before colon)
    /// Used by both trailing lambda and inline lambda parsing
    pub(crate) fn parse_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
        let mut params = Vec::new();
        // Check for no-param lambda: \: expr
        if !self.check(&TokenKind::Colon) {
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
            self.parse_remaining_lambda_params(&mut params)?;
        }
        Ok(params)
    }

    /// Parse lambda parameters between pipes: |x| or |x, y|
    /// Called after the opening pipe has been consumed.
    pub(crate) fn parse_pipe_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
        let mut params = Vec::new();
        // Check for no-param lambda: || expr
        if !self.check(&TokenKind::Pipe) {
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
            self.parse_remaining_lambda_params(&mut params)?;
        }
        Ok(params)
    }

    /// Helper to parse remaining comma-separated lambda parameters
    fn parse_remaining_lambda_params(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        while self.check(&TokenKind::Comma) {
            self.advance();
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
        }
        Ok(())
    }

    /// Try to parse a colon-block as a trailing lambda.
    ///
    /// Syntax:
    /// ```text
    /// func arg:
    ///     statement1
    ///     statement2
    /// ```
    ///
    /// This is parsed as `func(arg, fn(): statement1; statement2)`.
    ///
    /// Returns `Some(lambda)` if we see `:` followed by newline and indent,
    /// `None` if this doesn't look like a colon-block.
    fn try_parse_colon_block(&mut self) -> Result<Option<Expr>, ParseError> {
        // Must be at a colon
        if !self.check(&TokenKind::Colon) {
            return Ok(None);
        }

        // Peek ahead to see if this is a colon-block
        // We need: colon, newline, indent
        // Since we can't easily peek multiple tokens, we'll consume and check
        self.advance(); // consume ':'

        // Skip any newlines after the colon
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Must have indent for a block
        if !self.check(&TokenKind::Indent) {
            // Not a colon-block, but we already consumed the colon
            // This is an error state - colon without proper block
            return Err(ParseError::unexpected_token(
                "indented block after ':'",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }

        self.advance(); // consume Indent

        // Parse statements until dedent
        let mut statements = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
            // Skip newlines between statements
            while self.check(&TokenKind::Newline) {
                self.advance();
            }

            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                break;
            }

            let stmt = self.parse_item()?;
            statements.push(stmt);

            // Skip trailing newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume dedent if present
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        // Wrap statements in a DoBlock expression, then in a Lambda
        let block_expr = Expr::DoBlock(statements);

        Ok(Some(Expr::Lambda {
            params: vec![],
            body: Box::new(block_expr),
            move_mode: MoveMode::Copy,
        }))
    }

    /// Parse an if/elif expression (shared logic)
    pub(crate) fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        let condition = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let then_branch = self.parse_expression()?;
        let else_branch = if self.check(&TokenKind::Elif) {
            self.advance();
            Some(Box::new(self.parse_if_expr()?))
        } else if self.check(&TokenKind::Else) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        Ok(Expr::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch,
        })
    }

    pub(crate) fn parse_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();

        // Skip newlines and indent after opening paren (for multi-line argument lists)
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            self.advance();
        }

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            // Skip any stray whitespace tokens at the start of each argument
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
            {
                self.advance();
            }
            if self.check(&TokenKind::RParen) {
                break;
            }

            // Check for named argument with '=' or ':' syntax
            let mut name = None;
            if let TokenKind::Identifier(id) = &self.current.kind {
                let id_clone = id.clone();
                // Peek ahead for '=' or ':' without consuming the stream
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Assign {
                    name = Some(id_clone);
                    self.advance(); // consume identifier
                    self.expect(&TokenKind::Assign)?; // consume '='
                } else if next.kind == TokenKind::Colon {
                    // Support colon syntax: name: value
                    name = Some(id_clone);
                    self.advance(); // consume identifier
                    self.expect(&TokenKind::Colon)?; // consume ':'
                } else {
                    // leave current untouched; pending_token already holds the peeked token
                }
            }

            let value = self.parse_expression()?;
            args.push(Argument { name, value });

            // Skip newlines, indent, dedent after argument (for multi-line argument lists)
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
            {
                self.advance();
            }

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
                // Skip newlines, indent, dedent after comma
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(args)
    }

    /// Parse macro invocation arguments: !(args) or !{args} or ![args]
    pub(crate) fn parse_macro_args(&mut self) -> Result<Vec<MacroArg>, ParseError> {
        // Macros can use (), {}, or [] for their arguments
        let (_open, close) = if self.check(&TokenKind::LParen) {
            (TokenKind::LParen, TokenKind::RParen)
        } else if self.check(&TokenKind::LBrace) {
            (TokenKind::LBrace, TokenKind::RBrace)
        } else if self.check(&TokenKind::LBracket) {
            (TokenKind::LBracket, TokenKind::RBracket)
        } else {
            return Err(ParseError::unexpected_token(
                "'(', '{', or '['",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.advance(); // consume opening delimiter
        let mut args = Vec::new();

        while !self.check(&close) {
            // Try to parse as expression
            let expr = self.parse_expression()?;
            args.push(MacroArg::Expr(expr));

            if !self.check(&close) {
                // Allow comma or semicolon as separator
                if self.check(&TokenKind::Comma) || self.check(&TokenKind::Semicolon) {
                    self.advance();
                }
            }
        }

        self.expect(&close)?;
        Ok(args)
    }

    /// Parse comprehension clause: `for pattern in iterable [if condition]`
    /// Returns (pattern, iterable, condition)
    fn parse_comprehension_clause(
        &mut self,
    ) -> Result<(Pattern, Expr, Option<Box<Expr>>), ParseError> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        let condition = if self.check(&TokenKind::If) {
            self.advance();
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        Ok((pattern, iterable, condition))
    }

    /// Parse lambda body (params, colon, expression or block) with given move mode
    fn parse_lambda_body(&mut self, move_mode: MoveMode) -> Result<Expr, ParseError> {
        let params = self.parse_lambda_params()?;
        self.expect(&TokenKind::Colon)?;

        // Check if body is an indented block or inline expression
        let body = if self.check(&TokenKind::Newline) {
            // Peek ahead to see if we have a newline + indent (block body)
            if self.peek_is(&TokenKind::Indent) {
                // Parse as block
                let block = self.parse_block()?;
                Expr::DoBlock(block.statements)
            } else {
                // Just a newline, parse next expression
                self.parse_expression()?
            }
        } else {
            // Inline expression
            self.parse_expression()?
        };

        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode,
        })
    }

    /// Create a slice expression with the given components
    #[allow(dead_code)]
    fn make_slice(
        receiver: Expr,
        start: Option<Expr>,
        end: Option<Expr>,
        step: Option<Box<Expr>>,
    ) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }
}

// Primary expression parsing (extracted for maintainability)
include!("primary.rs");
