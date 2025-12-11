//! Expression parsing module
//!
//! This module contains all expression parsing logic for the Simple language parser.
//! It implements a Pratt parser (precedence climbing) for binary operators.

use crate::ast::*;
use crate::error::ParseError;
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
    // === Expression Parsing (Pratt Parser) ===

    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_or()
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
            // Check for no-parentheses call at statement level
            // Only for identifiers or field access followed by argument-starting tokens
            if self.is_callable_expr(&expr) && self.can_start_argument() {
                let args = self.parse_no_paren_arguments()?;
                if !args.is_empty() {
                    let call_expr = match expr {
                        Expr::Identifier(_) => Expr::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        Expr::FieldAccess { receiver, field } => Expr::MethodCall {
                            receiver,
                            method: field,
                            args,
                        },
                        _ => Expr::Call {
                            callee: Box::new(expr),
                            args,
                        },
                    };
                    return Ok(Node::Expression(call_expr));
                }
            }
            Ok(Node::Expression(expr))
        }
    }

    /// Check if an expression can be a callee for no-parens calls
    fn is_callable_expr(&self, expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::Identifier(_) | Expr::FieldAccess { .. } | Expr::Path(_)
        )
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

    /// Parse arguments without parentheses (comma-separated on same line)
    fn parse_no_paren_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        let mut args = Vec::new();

        // Parse first argument
        if let Ok(arg) = self.parse_single_argument() {
            args.push(arg);
        } else {
            return Ok(args);
        }

        // Parse remaining comma-separated arguments
        while self.check(&TokenKind::Comma) {
            self.advance();
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
                let value = self.parse_expression()?;
                return Ok(Argument {
                    name: Some(name_clone),
                    value,
                });
            }
        }
        // Positional argument
        let value = self.parse_expression()?;
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
                        let step = if self.check(&TokenKind::RBracket) {
                            None
                        } else {
                            Some(Box::new(self.parse_expression()?))
                        };
                        self.expect(&TokenKind::RBracket)?;
                        expr = Expr::Slice {
                            receiver: Box::new(expr),
                            start: None,
                            end: None,
                            step,
                        };
                    } else if self.check(&TokenKind::Colon) {
                        // Slice starting with : (no start)
                        self.advance();
                        // Check for ::step (no end)
                        if self.check(&TokenKind::Colon) {
                            self.advance();
                            let step = if self.check(&TokenKind::RBracket) {
                                None
                            } else {
                                Some(Box::new(self.parse_expression()?))
                            };
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: None,
                                end: None,
                                step,
                            };
                        } else {
                            let end = if self.check(&TokenKind::RBracket) {
                                None
                            } else {
                                Some(Box::new(self.parse_expression()?))
                            };
                            let step = if self.check(&TokenKind::Colon) {
                                self.advance();
                                if self.check(&TokenKind::RBracket) {
                                    None
                                } else {
                                    Some(Box::new(self.parse_expression()?))
                                }
                            } else {
                                None
                            };
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
                            let step = if self.check(&TokenKind::RBracket) {
                                None
                            } else {
                                Some(Box::new(self.parse_expression()?))
                            };
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
                            let step = if self.check(&TokenKind::Colon) {
                                self.advance();
                                if self.check(&TokenKind::RBracket) {
                                    None
                                } else {
                                    Some(Box::new(self.parse_expression()?))
                                }
                            } else {
                                None
                            };
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
                    let field = self.expect_identifier()?;
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
                TokenKind::Arrow => {
                    // Functional update operator: obj->method(args)
                    // Desugars to: obj = obj.method(args)
                    self.advance();
                    let method = self.expect_identifier()?;
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
        Ok(Expr::Call {
            callee: Box::new(callee),
            args,
        })
    }

    /// Parse a trailing block lambda: \params: body
    pub(crate) fn parse_trailing_lambda(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::Backslash)?;
        let mut params = Vec::new();

        // Check for no-param lambda: \: expr
        if !self.check(&TokenKind::Colon) {
            // Parse first param name
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });

            // Parse additional params (comma-separated)
            while self.check(&TokenKind::Comma) {
                self.advance();
                let name = self.expect_identifier()?;
                params.push(LambdaParam { name, ty: None });
            }
        }

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_expression()?;
        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode: MoveMode::Copy,
        })
    }

    pub(crate) fn parse_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();

        while !self.check(&TokenKind::RParen) {
            // Check for named argument
            let mut name = None;
            if let TokenKind::Identifier(id) = &self.current.kind {
                let id_clone = id.clone();
                // Peek ahead for '=' without consuming the stream
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Assign {
                    name = Some(id_clone);
                    self.advance(); // consume identifier
                    self.expect(&TokenKind::Assign)?; // consume '='
                } else {
                    // leave current untouched; pending_token already holds the peeked token
                }
            }

            let value = self.parse_expression()?;
            args.push(Argument { name, value });

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
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

    pub(crate) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Integer(n) => {
                let n = *n;
                self.advance();
                Ok(Expr::Integer(n))
            }
            TokenKind::TypedInteger(n, suffix) => {
                let n = *n;
                let suffix = suffix.clone();
                self.advance();
                Ok(Expr::TypedInteger(n, suffix))
            }
            TokenKind::Float(n) => {
                let n = *n;
                self.advance();
                Ok(Expr::Float(n))
            }
            TokenKind::TypedFloat(n, suffix) => {
                let n = *n;
                let suffix = suffix.clone();
                self.advance();
                Ok(Expr::TypedFloat(n, suffix))
            }
            TokenKind::String(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::String(s))
            }
            TokenKind::RawString(s) => {
                // Raw strings are just plain strings with no interpolation
                let s = s.clone();
                self.advance();
                Ok(Expr::String(s))
            }
            TokenKind::FString(parts) => {
                let parts = parts.clone();
                self.advance();
                let mut result_parts = Vec::new();
                for part in parts {
                    match part {
                        FStringToken::Literal(s) => {
                            result_parts.push(FStringPart::Literal(s));
                        }
                        FStringToken::Expr(expr_str) => {
                            // Parse the expression string
                            let mut sub_parser = Parser::new(&expr_str);
                            match sub_parser.parse_expression() {
                                Ok(expr) => result_parts.push(FStringPart::Expr(expr)),
                                Err(e) => return Err(e),
                            }
                        }
                    }
                }
                Ok(Expr::FString(result_parts))
            }
            TokenKind::Bool(b) => {
                let b = *b;
                self.advance();
                Ok(Expr::Bool(b))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Expr::Nil)
            }
            TokenKind::Symbol(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::Symbol(s))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();
                // Check for path expression: Name::Variant
                if self.check(&TokenKind::DoubleColon) {
                    let mut segments = vec![name];
                    while self.check(&TokenKind::DoubleColon) {
                        self.advance(); // consume '::'
                        let segment = self.expect_identifier()?;
                        segments.push(segment);
                    }
                    Ok(Expr::Path(segments))
                // Check for struct initialization: Name { field: value, ... }
                // Convention: struct names start with uppercase
                } else if self.check(&TokenKind::LBrace)
                    && name.chars().next().map_or(false, |c| c.is_uppercase())
                {
                    self.advance(); // consume '{'
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        self.expect(&TokenKind::Colon)?;
                        let value = self.parse_expression()?;
                        fields.push((field_name, value));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    Ok(Expr::StructInit { name, fields })
                } else {
                    Ok(Expr::Identifier(name))
                }
            }
            TokenKind::Self_ => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
            TokenKind::Backslash => {
                // Lambda: \x: expr or \x, y: expr or \: expr
                self.advance();
                let mut params = Vec::new();

                // Check for no-param lambda: \: expr
                if !self.check(&TokenKind::Colon) {
                    // Parse first param name
                    let name = self.expect_identifier()?;
                    params.push(LambdaParam { name, ty: None });

                    // Parse additional params (comma-separated)
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        let name = self.expect_identifier()?;
                        params.push(LambdaParam { name, ty: None });
                    }
                }

                self.expect(&TokenKind::Colon)?;
                let body = self.parse_expression()?;
                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                    move_mode: MoveMode::Copy,
                })
            }
            TokenKind::Move => {
                // Move closure: move \x: expr
                self.advance();
                // Expect the backslash for lambda
                if !self.check(&TokenKind::Backslash) {
                    return Err(ParseError::unexpected_token(
                        "'\\'",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
                self.advance();
                let mut params = Vec::new();

                // Check for no-param lambda: move \: expr
                if !self.check(&TokenKind::Colon) {
                    let name = self.expect_identifier()?;
                    params.push(LambdaParam { name, ty: None });

                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        let name = self.expect_identifier()?;
                        params.push(LambdaParam { name, ty: None });
                    }
                }

                self.expect(&TokenKind::Colon)?;
                let body = self.parse_expression()?;
                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                    move_mode: MoveMode::Move,
                })
            }
            TokenKind::LParen => {
                self.advance();
                // Check for lambda: (x, y) => expr
                // Or tuple: (1, 2, 3)
                // Or grouping: (expr)
                if self.check(&TokenKind::RParen) {
                    self.advance();
                    // Empty tuple or lambda with no params
                    if self.check(&TokenKind::FatArrow) {
                        self.advance();
                        let body = self.parse_expression()?;
                        return Ok(Expr::Lambda {
                            params: vec![],
                            body: Box::new(body),
                            move_mode: MoveMode::Copy,
                        });
                    }
                    return Ok(Expr::Tuple(vec![]));
                }

                let first = self.parse_expression()?;

                if self.check(&TokenKind::Comma) {
                    // Tuple
                    let mut elements = vec![first];
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        elements.push(self.parse_expression()?);
                    }
                    self.expect(&TokenKind::RParen)?;
                    Ok(Expr::Tuple(elements))
                } else {
                    // Grouping
                    self.expect(&TokenKind::RParen)?;
                    Ok(first)
                }
            }
            TokenKind::LBracket => {
                self.advance();
                // Empty array
                if self.check(&TokenKind::RBracket) {
                    self.advance();
                    return Ok(Expr::Array(Vec::new()));
                }

                // Check for spread operator
                if self.check(&TokenKind::Star) {
                    return self.parse_array_with_spreads();
                }

                // Parse first expression
                let first = self.parse_expression()?;

                // Check for list comprehension: [expr for pattern in iterable]
                if self.check(&TokenKind::For) {
                    self.advance();
                    let pattern = self.parse_pattern()?;
                    self.expect(&TokenKind::In)?;
                    let iterable = self.parse_expression()?;
                    let condition = if self.check(&TokenKind::If) {
                        self.advance();
                        Some(Box::new(self.parse_expression()?))
                    } else {
                        None
                    };
                    self.expect(&TokenKind::RBracket)?;
                    return Ok(Expr::ListComprehension {
                        expr: Box::new(first),
                        pattern,
                        iterable: Box::new(iterable),
                        condition,
                    });
                }

                // Regular array
                let mut elements = vec![first];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                    // Check for spread in middle of array
                    if self.check(&TokenKind::Star) {
                        self.advance();
                        elements.push(Expr::Spread(Box::new(self.parse_expression()?)));
                    } else {
                        elements.push(self.parse_expression()?);
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Expr::Array(elements))
            }
            TokenKind::LBrace => {
                self.advance();
                // Empty dict
                if self.check(&TokenKind::RBrace) {
                    self.advance();
                    return Ok(Expr::Dict(Vec::new()));
                }

                // Check for dict spread: {**d1, **d2}
                if self.check(&TokenKind::DoubleStar) {
                    return self.parse_dict_with_spreads();
                }

                // Parse first key
                let key = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let value = self.parse_expression()?;

                // Check for dict comprehension: {k: v for pattern in iterable}
                if self.check(&TokenKind::For) {
                    self.advance();
                    let pattern = self.parse_pattern()?;
                    self.expect(&TokenKind::In)?;
                    let iterable = self.parse_expression()?;
                    let condition = if self.check(&TokenKind::If) {
                        self.advance();
                        Some(Box::new(self.parse_expression()?))
                    } else {
                        None
                    };
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Expr::DictComprehension {
                        key: Box::new(key),
                        value: Box::new(value),
                        pattern,
                        iterable: Box::new(iterable),
                        condition,
                    });
                }

                // Regular dict
                let mut pairs = vec![(key, value)];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    if self.check(&TokenKind::RBrace) {
                        break;
                    }
                    // Check for spread: **dict
                    if self.check(&TokenKind::DoubleStar) {
                        self.advance(); // **
                        let spread_expr = self.parse_expression()?;
                        // Use a sentinel key to mark spread
                        pairs.push((Expr::DictSpread(Box::new(spread_expr)), Expr::Nil));
                    } else {
                        let k = self.parse_expression()?;
                        self.expect(&TokenKind::Colon)?;
                        let v = self.parse_expression()?;
                        pairs.push((k, v));
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                Ok(Expr::Dict(pairs))
            }
            TokenKind::Spawn => {
                self.advance();
                let expr = self.parse_expression()?;
                Ok(Expr::Spawn(Box::new(expr)))
            }
            TokenKind::New => {
                self.advance();
                // new &Type(...) or new *Type(...)
                let kind = match &self.current.kind {
                    TokenKind::Ampersand => {
                        self.advance();
                        PointerKind::Unique
                    }
                    TokenKind::Star => {
                        self.advance();
                        PointerKind::Shared
                    }
                    TokenKind::Minus => {
                        self.advance();
                        PointerKind::Weak
                    }
                    TokenKind::Plus => {
                        self.advance();
                        PointerKind::Handle
                    }
                    _ => PointerKind::Shared, // default
                };
                let expr = self.parse_postfix()?;
                Ok(Expr::New {
                    kind,
                    expr: Box::new(expr),
                })
            }
            TokenKind::If => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let then_branch = self.parse_expression()?;
                let else_branch = if self.check(&TokenKind::Elif) {
                    Some(Box::new(self.parse_primary()?))
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
            TokenKind::Elif => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let then_branch = self.parse_expression()?;
                let else_branch = if self.check(&TokenKind::Elif) {
                    Some(Box::new(self.parse_primary()?))
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
            TokenKind::Match => {
                self.advance();
                let subject = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                if self.check(&TokenKind::Newline) {
                    self.advance();
                    self.expect(&TokenKind::Indent)?;
                    let mut arms = Vec::new();
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) {
                            break;
                        }
                        arms.push(self.parse_match_arm_expr()?);
                    }
                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }
                    Ok(Expr::Match {
                        subject: Box::new(subject),
                        arms,
                    })
                } else {
                    Err(ParseError::unexpected_token(
                        "newline after match",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
            TokenKind::Dollar => {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(Expr::Identifier(format!("${}", name)))
            }
            _ => Err(ParseError::unexpected_token(
                "expression",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_match_arm_expr(&mut self) -> Result<MatchArm, ParseError> {
        use crate::token::Span;
        let start_span = self.current.span;
        let pattern = self.parse_pattern()?;
        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };
        self.expect(&TokenKind::FatArrow)?;
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
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            guard,
            body,
        })
    }
}
