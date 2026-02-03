use crate::ast::{Argument, Expr, LambdaParam, MoveMode};
use crate::error::ParseError;
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
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

    /// Check if an expression is a simple type identifier (starting with uppercase)
    /// Used to detect static method calls like `Duration.new()` vs instance calls like `obj.method()`
    /// Note: This only returns true for simple identifiers, NOT field accesses like `module.Type`
    /// Field accesses are handled differently - they remain as MethodCall and the interpreter
    /// resolves the type from the module.
    fn is_type_path(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Identifier(name) => name.chars().next().map_or(false, |c| c.is_uppercase()),
            // Don't convert field accesses to paths - let the interpreter handle module.Type.method()
            _ => false,
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
                    // Only treat [ as indexing if it's adjacent to the previous token
                    // (no whitespace between). This allows `expect [1, 2, 3]` to work
                    // where [1, 2, 3] is a separate argument, not indexing.
                    // Check: if previous token's end != current token's start, there's whitespace
                    if self.previous.span.end != self.current.span.start {
                        // Not adjacent - break to let no-paren call handling deal with it
                        break;
                    }
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
                        } else if self.check(&TokenKind::Colon) || matches!(&self.current.kind, TokenKind::Symbol(_)) {
                            // It's a slice
                            // Handle Symbol tokens as :identifier (e.g., arr[start:end] where :end is Symbol("end"))
                            // Note: Symbol tokens like :self may be followed by postfix operators (e.g., :self.pos)
                            // so we need to parse them as full expressions
                            let end = if let TokenKind::Symbol(name) = &self.current.kind.clone() {
                                // Symbol like :name means the colon was absorbed into the token
                                // Convert Symbol(name) back to Identifier so parse_expression can handle it
                                // This allows binary operators like `arr[0:n - 1]` to work
                                let name = name.clone();
                                let span = self.current.span.clone();
                                self.advance(); // consume the Symbol token

                                // Create an identifier token and set it as current
                                use crate::token::NamePattern;
                                let ident_token = crate::token::Token {
                                    kind: TokenKind::Identifier {
                                        name: name.clone(),
                                        pattern: NamePattern::Immutable,
                                    },
                                    lexeme: name,
                                    span,
                                };
                                // Put what was going to be current into pending, then set ident as current
                                self.pending_tokens.push_front(self.current.clone());
                                self.current = ident_token;

                                // Now let parse_expression handle the full expression including binary ops
                                Some(Box::new(self.parse_expression()?))
                            } else {
                                self.advance(); // consume the colon
                                if self.check(&TokenKind::Colon) || self.check(&TokenKind::RBracket) {
                                    None
                                } else {
                                    Some(Box::new(self.parse_expression()?))
                                }
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
                                args.push(Argument::new(None, trailing_lambda));
                            }
                            // Check if this is a static method call: Type.method()
                            // Indicated by receiver being a type name (uppercase first letter)
                            if self.is_type_path(&expr) {
                                // Static method call: convert to Path + Call
                                let mut path_segments = self.field_access_to_path_segments(&expr)?;
                                path_segments.push(field);
                                expr = Expr::Call {
                                    callee: Box::new(Expr::Path(path_segments)),
                                    args,
                                };
                            } else {
                                expr = Expr::MethodCall {
                                    receiver: Box::new(expr),
                                    method: field,
                                    args,
                                };
                            }
                        } else if self.check(&TokenKind::Backslash) {
                            // Method call with only trailing block: obj.method \x: body
                            let trailing_lambda = self.parse_trailing_lambda()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument::new(None, trailing_lambda)],
                            };
                        } else if self.check(&TokenKind::LBrace)
                            && !self.no_brace_postfix
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
                        } else if self.check(&TokenKind::LBrace) && !self.no_brace_postfix {
                            // Method call with dict argument: obj.method {...}
                            // Parse the dict as the single argument
                            let dict_expr = self.parse_expression()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument::new(None, dict_expr)],
                            };
                        } else {
                            expr = Expr::FieldAccess {
                                receiver: Box::new(expr),
                                field,
                            };
                        }

                        // Check for :: after field access (e.g., torch.Device::CPU)
                        // Convert FieldAccess to Path for static method calls
                        // DEPRECATED: Use dot syntax instead (torch.Device.CPU)
                        if self.check(&TokenKind::DoubleColon) {
                            // Emit deprecation warning for :: syntax
                            let colon_span = self.current.span;
                            let warning = ErrorHint {
                                level: ErrorHintLevel::Warning,
                                message: "Use dot (.) instead of double colon (::) for static methods and enum variants".to_string(),
                                span: colon_span,
                                suggestion: Some("Replace '::' with '.' - Simple uses dot notation for all member access".to_string()),
                                help: Some("Examples: Type.new() not Type::new(), Option.Some(x) not Option::Some(x), Point.origin() not Point::origin()".to_string()),
                            };
                            self.error_hints.push(warning);

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
                TokenKind::DoubleQuestion => {
                    // Null coalescing / Option fallback: expr ?? default
                    self.advance();
                    let default = self.parse_unary()?; // Higher precedence than ??
                    expr = Expr::Coalesce {
                        expr: Box::new(expr),
                        default: Box::new(default),
                    };
                }
                TokenKind::QuestionDot => {
                    // Optional chaining: expr?.field or expr?.method(args)
                    self.advance();
                    let field = self.expect_method_name()?;
                    if self.check(&TokenKind::LParen) {
                        let args = self.parse_arguments()?;
                        expr = Expr::OptionalMethodCall {
                            receiver: Box::new(expr),
                            method: field,
                            args,
                        };
                    } else {
                        expr = Expr::OptionalChain {
                            expr: Box::new(expr),
                            field,
                        };
                    }
                }
                TokenKind::DotQuestion => {
                    // Existence check: expr.? - returns bool (is present/non-empty)
                    self.advance();
                    expr = Expr::ExistsCheck(Box::new(expr));
                }
                TokenKind::Unwrap => {
                    // Safe unwrap: expr unwrap or: default / expr unwrap else: fn / expr unwrap or_return:
                    self.advance();
                    match &self.current.kind {
                        TokenKind::OrColon => {
                            self.advance();
                            let default = self.parse_expression()?;
                            expr = Expr::UnwrapOr {
                                expr: Box::new(expr),
                                default: Box::new(default),
                            };
                        }
                        TokenKind::Else => {
                            // Check for else: (Else followed by Colon)
                            self.advance();
                            self.expect(&TokenKind::Colon)?;
                            let fallback_fn = self.parse_expression()?;
                            expr = Expr::UnwrapElse {
                                expr: Box::new(expr),
                                fallback_fn: Box::new(fallback_fn),
                            };
                        }
                        TokenKind::OrReturn => {
                            self.advance();
                            expr = Expr::UnwrapOrReturn(Box::new(expr));
                        }
                        _ => {
                            return Err(ParseError::syntax_error_with_span(
                                "unwrap requires 'or:', 'else:', or 'or_return:' suffix".to_string(),
                                self.current.span,
                            ));
                        }
                    }
                }
                TokenKind::As => {
                    // Type cast: expr as Type [or: default | else: fn | or_return:]
                    self.advance();
                    let target_type = self.parse_type()?;

                    // Check for fallback suffix
                    match &self.current.kind {
                        TokenKind::OrColon => {
                            self.advance();
                            let default = self.parse_expression()?;
                            expr = Expr::CastOr {
                                expr: Box::new(expr),
                                target_type,
                                default: Box::new(default),
                            };
                        }
                        TokenKind::Else => {
                            // Check for else: (Else followed by Colon)
                            self.advance();
                            self.expect(&TokenKind::Colon)?;
                            let fallback_fn = self.parse_expression()?;
                            expr = Expr::CastElse {
                                expr: Box::new(expr),
                                target_type,
                                fallback_fn: Box::new(fallback_fn),
                            };
                        }
                        TokenKind::OrReturn => {
                            self.advance();
                            expr = Expr::CastOrReturn {
                                expr: Box::new(expr),
                                target_type,
                            };
                        }
                        _ => {
                            // Plain cast - no fallback
                            expr = Expr::Cast {
                                expr: Box::new(expr),
                                target_type,
                            };
                        }
                    }
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
            args.push(Argument::new(None, trailing_lambda));
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
        let (params, capture_all) = self.parse_lambda_params()?;
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
            capture_all,
        })
    }

    /// Parse lambda parameters (comma-separated identifiers before colon)
    /// Used by both trailing lambda and inline lambda parsing
    /// Supports \ *: for capture-all syntax
    /// Supports \_ for wildcard/discard parameter
    pub(crate) fn parse_lambda_params(&mut self) -> Result<(Vec<LambdaParam>, bool), ParseError> {
        let mut params = Vec::new();
        let mut capture_all = false;

        // Check for capture-all: \ *:
        if self.check(&TokenKind::Star) {
            self.advance();
            capture_all = true;
        }
        // Check for no-param lambda: \: expr (also treated as capture-all)
        else if !self.check(&TokenKind::Colon) {
            // Check for wildcard parameter: \_
            let name = if self.check(&TokenKind::Underscore) {
                self.advance();
                "_".to_string()
            } else {
                self.expect_identifier()?
            };
            params.push(LambdaParam { name, ty: None });
            self.parse_remaining_lambda_params(&mut params)?;
        } else {
            // Empty params with just \: means capture all
            capture_all = true;
        }
        Ok((params, capture_all))
    }

    /// Parse lambda parameters between pipes: |x| or |x, y| or |_|
    /// Called after the opening pipe has been consumed.
    pub(crate) fn parse_pipe_lambda_params(&mut self) -> Result<Vec<LambdaParam>, ParseError> {
        let mut params = Vec::new();
        // Check for no-param lambda: || expr
        if !self.check(&TokenKind::Pipe) {
            // Check for wildcard parameter: |_|
            let name = if self.check(&TokenKind::Underscore) {
                self.advance();
                "_".to_string()
            } else {
                self.expect_identifier()?
            };
            params.push(LambdaParam { name, ty: None });
            self.parse_remaining_lambda_params(&mut params)?;
        }
        Ok(params)
    }
}
