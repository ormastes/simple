use crate::ast::{Argument, Expr, LambdaParam, MoveMode};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    /// Convert an expression to a qualified name (e.g., a.b.c -> "a.b.c")
    fn expr_to_qualified_name(&self, expr: Expr) -> Result<String, ParseError> {
        match expr {
            Expr::Identifier(name) => Ok(name),
            Expr::FieldAccess { receiver, field } => {
                let receiver_name = self.expr_to_qualified_name(*receiver)?;
                Ok(format!("{}.{}", receiver_name, field))
            }
            _ => Err(ParseError::syntax_error_with_span(
                "Expected qualified name (identifier or field access)".to_string(),
                self.current.span,
            )),
        }
    }

    /// Convert a FieldAccess chain to path segments (e.g., torch.Device -> ["torch", "Device"])
    fn field_access_to_path_segments(&self, expr: &Expr) -> Result<Vec<String>, ParseError> {
        match expr {
            Expr::Identifier(name) => Ok(vec![name.clone()]),
            Expr::FieldAccess { receiver, field } => {
                let mut segments = self.field_access_to_path_segments(receiver)?;
                segments.push(field.clone());
                Ok(segments)
            }
            _ => Err(ParseError::syntax_error_with_span(
                "Expected path expression (identifier or field access)".to_string(),
                self.current.span,
            )),
        }
    }

    pub(crate) fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;
        // Track indents consumed for multi-line method chaining
        let mut consumed_indents: usize = 0;

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

                        // In LL(1) mode, process the macro contract to register introduced symbols
                        if self.macro_registry.is_ll1_mode() {
                            self.process_macro_contract_ll1(&name, &args);
                        }

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
                            let end = if self.check(&TokenKind::Colon) || self.check(&TokenKind::RBracket) {
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
                    // Skip newlines and indents after dot for multi-line chaining: obj.\n    method()
                    while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
                        if matches!(self.current.kind, TokenKind::Indent) {
                            consumed_indents += 1;
                        }
                        self.advance();
                    }
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
                        } else if self.check(&TokenKind::LBrace)
                            && field.chars().next().map_or(false, |c| c.is_uppercase())
                        {
                            // Qualified struct initialization: module.StructName { ... }
                            // Convert receiver.field to qualified name
                            let qualified_name = self.expr_to_qualified_name(expr)?;
                            let full_name = format!("{}.{}", qualified_name, field);

                            self.advance(); // consume '{'
                                            // Skip newlines after opening brace
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            let mut fields = Vec::new();
                            while !self.check(&TokenKind::RBrace) {
                                let field_name = self.expect_identifier()?;
                                // Skip newlines before colon or comma
                                while self.check(&TokenKind::Newline) {
                                    self.advance();
                                }

                                // Check for shorthand syntax
                                let value = if self.check(&TokenKind::Colon) {
                                    self.advance(); // consume ':'
                                    while self.check(&TokenKind::Newline) {
                                        self.advance();
                                    }
                                    self.parse_expression()?
                                } else {
                                    Expr::Identifier(field_name.clone())
                                };

                                while self.check(&TokenKind::Newline) {
                                    self.advance();
                                }
                                fields.push((field_name, value));
                                if !self.check(&TokenKind::RBrace) {
                                    self.expect(&TokenKind::Comma)?;
                                    while self.check(&TokenKind::Newline) {
                                        self.advance();
                                    }
                                }
                            }
                            self.expect(&TokenKind::RBrace)?;
                            expr = Expr::StructInit {
                                name: full_name,
                                fields,
                            };
                        } else {
                            expr = Expr::FieldAccess {
                                receiver: Box::new(expr),
                                field,
                            };
                        }

                        // Check for :: after field access (e.g., torch.Device::CPU)
                        // Convert FieldAccess to Path for static method calls
                        if self.check(&TokenKind::DoubleColon) {
                            // Convert expr (which is now a FieldAccess) to a path
                            let path_segments = self.field_access_to_path_segments(&expr)?;
                            let mut segments = path_segments;

                            while self.check(&TokenKind::DoubleColon) {
                                self.advance(); // consume '::'
                                let segment = self.expect_method_name()?;
                                segments.push(segment);
                            }

                            expr = Expr::Path(segments);
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
                TokenKind::As => {
                    // Type cast: expr as Type
                    self.advance();
                    let target_type = self.parse_type()?;
                    expr = Expr::Cast {
                        expr: Box::new(expr),
                        target_type,
                    };
                }
                TokenKind::Newline => {
                    // Multi-line method chaining: obj.method()\n    .another()
                    // Check if a dot follows after newlines/indents
                    if self.peek_through_newlines_and_indents_is(&TokenKind::Dot) {
                        consumed_indents += self.skip_newlines_and_indents_for_method_chain();
                        // Now self.current should be Dot, continue the loop
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }

        // Don't consume DEDENTs here - leave them for the statement parser.
        // The INDENTs we consumed are "continuation indents" that don't create new blocks.
        // We need to peek and consume them if they're immediately after NEWLINEs.
        if consumed_indents > 0 {
            // Peek through NEWLINEs to consume matching DEDENTs
            while consumed_indents > 0 {
                if matches!(self.current.kind, TokenKind::Newline) {
                    // Look ahead to see if DEDENT follows
                    let next_is_dedent = self
                        .pending_tokens
                        .front()
                        .map(|t| matches!(t.kind, TokenKind::Dedent))
                        .unwrap_or(false);
                    if next_is_dedent {
                        self.advance(); // consume NEWLINE
                        self.advance(); // consume DEDENT
                        consumed_indents -= 1;
                    } else {
                        break;
                    }
                } else if matches!(self.current.kind, TokenKind::Dedent) {
                    self.advance();
                    consumed_indents -= 1;
                } else {
                    break;
                }
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
}
