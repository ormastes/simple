use crate::ast::{Argument, BinOp, Expr, LambdaParam, MoveMode, Type, UnaryOp};
use crate::error::ParseError;
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
use crate::expressions::placeholder::{force_transform_placeholder_lambda, transform_placeholder_lambda};
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    /// If the current token is a `Symbol(name)` literal, rewrite it in place into
    /// an `Identifier` token and return true; otherwise leave the stream alone and
    /// return false.
    ///
    /// The lexer fuses `:` immediately followed by an identifier character into a
    /// single symbol-literal token, so inside a subscript the colon that opens a
    /// slice bound is swallowed: `xs[:end]` arrives as `Symbol("end")` rather than
    /// `Colon` + `Identifier`, and `xs[a:end]` likewise. Handing the name back as an
    /// identifier lets `parse_expression` parse the full bound (including binary
    /// operators and postfix, e.g. `xs[a:n - 1]` or `xs[:obj.len]`).
    fn rewrite_symbol_as_identifier(&mut self) -> bool {
        let TokenKind::Symbol(name) = &self.current.kind else {
            return false;
        };
        let name = name.clone();
        let span = self.current.span;
        self.advance(); // consume the Symbol token

        use crate::token::NamePattern;
        let ident_token = crate::token::Token {
            kind: TokenKind::Identifier {
                name: name.clone(),
                pattern: NamePattern::Immutable,
            },
            lexeme: name,
            span,
        };
        // Push what advance() made current back into pending, then install the
        // rewritten identifier as current so parse_expression sees `name ...`.
        self.pending_tokens.push_front(self.current.clone());
        self.current = ident_token;
        true
    }

    fn transform_placeholder_args_for_call(&self, callee: &Expr, args: &mut [Argument]) {
        if Self::expr_is_higher_order_callee(callee) {
            for arg in args {
                let value = std::mem::replace(&mut arg.value, Expr::Nil);
                arg.value = force_transform_placeholder_lambda(value);
            }
            return;
        }
        if self.call_arg_depth > 0 {
            return;
        }
        for arg in args {
            let value = std::mem::replace(&mut arg.value, Expr::Nil);
            arg.value = transform_placeholder_lambda(value);
        }
    }

    fn expr_is_higher_order_callee(callee: &Expr) -> bool {
        match callee {
            Expr::Identifier(name) => Self::name_is_higher_order_callback_callee(name),
            Expr::FieldAccess { field, .. } => Self::name_is_higher_order_callback_callee(field),
            Expr::Path(parts) => parts
                .last()
                .is_some_and(|name| Self::name_is_higher_order_callback_callee(name)),
            _ => false,
        }
    }

    fn name_is_higher_order_callback_callee(name: &str) -> bool {
        matches!(
            name,
            "map"
                | "mapped"
                | "filter"
                | "reject"
                | "any"
                | "all"
                | "each"
                | "for_each"
                | "flat_map"
                | "compact_map"
                | "map_err"
                | "and_then"
                | "then"
                | "reduce"
                | "fold"
        ) || name.ends_with("_map")
            || name.ends_with("_filter")
            || name.ends_with("_any")
            || name.ends_with("_all")
            || name.ends_with("_each")
    }

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

    fn validate_bracket_operand(&self, expr: &Expr, context: &str) -> Result<(), ParseError> {
        match expr {
            Expr::Binary {
                op:
                    BinOp::Eq
                    | BinOp::NotEq
                    | BinOp::Lt
                    | BinOp::Gt
                    | BinOp::LtEq
                    | BinOp::GtEq
                    | BinOp::And
                    | BinOp::Or
                    | BinOp::AndSuspend
                    | BinOp::OrSuspend,
                ..
            } => Err(ParseError::syntax_error_with_span(
                format!("{context} cannot be a comparison or logical expression inside []"),
                self.previous.span,
            )),
            Expr::Unary { op: UnaryOp::Not, .. } => Err(ParseError::syntax_error_with_span(
                format!("{context} cannot use `not` inside []"),
                self.previous.span,
            )),
            _ => Ok(()),
        }
    }

    fn validate_optional_bracket_operand(&self, expr: &Option<Box<Expr>>, context: &str) -> Result<(), ParseError> {
        if let Some(expr) = expr {
            self.validate_bracket_operand(expr, context)?;
        }
        Ok(())
    }

    pub(crate) fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;
        // Track indents consumed for multi-line method chaining
        let mut consumed_indents: usize = 0;

        loop {
            match &self.current.kind {
                TokenKind::LParen => {
                    // Only treat `(` as parenthesized call arguments if it's
                    // adjacent to the previous token (no whitespace between),
                    // mirroring the LBracket adjacency check below. With a
                    // space before it — `print (16.0).sqrt()` — the `(...)`
                    // is a parenthesized sub-expression that the no-paren
                    // call machinery (parse_with_no_paren_calls) should parse
                    // as the first ARGUMENT, postfix chain and all, not as
                    // this callee's own call parens. Without this check,
                    // `print (16.0).sqrt()` parsed as
                    // `(print(16.0)).sqrt()` — print fired with the
                    // un-sqrt'd 16.0 and the sqrt() applied (and discarded)
                    // to print's return value, so callers only ever saw the
                    // un-rooted "16.0". See
                    // doc/08_tracking/bug/float_literal_receiver_method_call_returns_receiver_2026-08-10.md
                    if self.previous.span.end != self.current.span.start {
                        break;
                    }
                    expr = self.parse_call(expr)?;
                }
                TokenKind::TripleLt => {
                    // CUDA kernel launch: kernel<<<grid: expr, block: expr>>>(args)
                    expr = self.parse_kernel_launch(expr)?;
                }
                TokenKind::Bang => {
                    // Disambiguate: name!(args) is macro invocation,
                    // expr! (anything else) is force unwrap.
                    if let Expr::Identifier(ref name) = expr {
                        // Peek past `!`: if `(` follows → macro invocation,
                        // otherwise → force unwrap of a bare variable.
                        let after_bang = self.peek_next();
                        if after_bang.kind == TokenKind::LParen {
                            let name = name.clone();
                            self.advance(); // consume !
                            let args = self.parse_macro_args()?;

                            // In LL(1) mode, process the macro contract to register introduced symbols
                            if self.macro_registry.is_ll1_mode() {
                                self.process_macro_contract_ll1(&name, &args);
                            }

                            expr = Expr::MacroInvocation { name, args };
                        } else {
                            // Force unwrap: variable!
                            self.advance(); // consume !
                            expr = Expr::ForceUnwrap(Box::new(expr));
                        }
                    } else {
                        // Force unwrap on any non-identifier expression: expr!
                        self.advance(); // consume !
                        expr = Expr::ForceUnwrap(Box::new(expr));
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
                    } else if matches!(&self.current.kind, TokenKind::Symbol(_)) {
                        // Slice starting with : (no start) whose end bound begins with
                        // an identifier: `xs[:end]`. The lexer fused the opening colon
                        // into a symbol literal (`:end` -> Symbol("end")), so this never
                        // reached the Colon branch below and instead fell through to the
                        // plain-index path — silently turning `xs[:end]` into `xs[end]`.
                        // Mirrors the same rewrite on the `xs[start:end]` path.
                        self.rewrite_symbol_as_identifier();
                        let end = Some(Box::new(self.parse_expression()?));
                        self.validate_optional_bracket_operand(&end, "slice end")?;
                        let step = self.parse_optional_step()?;
                        self.validate_optional_bracket_operand(&step, "slice step")?;
                        self.expect(&TokenKind::RBracket)?;
                        expr = Expr::Slice {
                            receiver: Box::new(expr),
                            start: None,
                            end,
                            step,
                        };
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
                            self.validate_bracket_operand(&first, "slice start")?;
                            self.advance();
                            let step = self.parse_optional_expr_before_bracket()?;
                            self.validate_optional_bracket_operand(&step, "slice step")?;
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
                            let end = if self.rewrite_symbol_as_identifier() {
                                // Symbol like :name means the colon was absorbed into the
                                // token; it has been handed back as an identifier, so let
                                // parse_expression handle the full bound including binary
                                // ops (e.g. `arr[0:n - 1]`).
                                Some(Box::new(self.parse_expression()?))
                            } else {
                                self.advance(); // consume the colon
                                if self.check(&TokenKind::Colon) || self.check(&TokenKind::RBracket) {
                                    None
                                } else {
                                    Some(Box::new(self.parse_expression()?))
                                }
                            };
                            self.validate_bracket_operand(&first, "slice start")?;
                            self.validate_optional_bracket_operand(&end, "slice end")?;
                            let step = self.parse_optional_step()?;
                            self.validate_optional_bracket_operand(&step, "slice step")?;
                            self.expect(&TokenKind::RBracket)?;
                            expr = Expr::Slice {
                                receiver: Box::new(expr),
                                start: Some(Box::new(first)),
                                end,
                                step,
                            };
                        } else {
                            // Regular index access
                            self.validate_bracket_operand(&first, "index expression")?;
                            self.expect(&TokenKind::RBracket)?;
                            // B4: rewrite `x.bits[lo..hi]` to mask+shift at parse time.
                            // Falls through unchanged for non-`.bits` indices, and is
                            // skipped when the next token is an assignment operator so
                            // that `parse_expression_or_assignment` can desugar the
                            // write side (which needs the original Index/Range shape).
                            //
                            // Safe vs `==`: comparison operators are distinct token
                            // kinds (`Eq`, `NotEq`, ...), so the assignment-token peek
                            // does not collide with `x.bits[…] == y`.
                            let raw = Expr::Index {
                                receiver: Box::new(expr),
                                index: Box::new(first),
                            };
                            expr = if matches!(
                                self.current.kind,
                                TokenKind::Assign
                                    | TokenKind::PlusAssign
                                    | TokenKind::MinusAssign
                                    | TokenKind::StarAssign
                                    | TokenKind::SlashAssign
                                    | TokenKind::PercentAssign
                                    | TokenKind::TildeAssign
                                    | TokenKind::TildePlusAssign
                                    | TokenKind::TildeMinusAssign
                                    | TokenKind::TildeStarAssign
                                    | TokenKind::TildeSlashAssign
                            ) {
                                raw
                            } else {
                                super::bitfield::maybe_rewrite_bits_read(raw)
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
                    // NESTED tuple access: `r.0.1`.
                    //
                    // seed_nested_tuple_index_float_munch_2026-08-06: the lexer
                    // is context-free and has already munched the `0.1` after
                    // the first `.` into a single Float token, so the arm above
                    // never sees an Integer and the parser died with
                    // `expected identifier, found Float(0.1)`. The information
                    // needed to undo this is in the token's LEXEME, not its
                    // f64 value: `.0.10` and `.0.1` both parse to 0.1, and
                    // 0.30000000000000004-style values make the f64 unusable as
                    // an index source. So we re-split the raw text.
                    //
                    // Deliberately conservative -- only a lexeme of the exact
                    // shape `digits.digits` (no sign, no exponent, no `_`
                    // separators, no numeric suffix, and TokenKind::Float, so a
                    // TypedFloat like `0.1f32` is excluded) is reinterpreted.
                    // Anything else stays a genuine float and falls through to
                    // the existing error, because a real float can never
                    // legally follow `.` anyway.
                    } else if let Some((a, b)) = match &self.current.kind {
                        TokenKind::Float(_) => split_tuple_index_pair(&self.current.lexeme),
                        _ => None,
                    } {
                        self.advance();
                        expr = Expr::TupleIndex {
                            receiver: Box::new(Expr::TupleIndex {
                                receiver: Box::new(expr),
                                index: a,
                            }),
                            index: b,
                        };
                    // Support computed field access: children.(idx - 1)
                    } else if self.check(&TokenKind::LParen) {
                        self.advance(); // consume '('
                        let index_expr = self.parse_expression()?;
                        self.expect(&TokenKind::RParen)?;
                        expr = Expr::Index {
                            receiver: Box::new(expr),
                            index: Box::new(index_expr),
                        };
                    } else {
                        let field = self.expect_method_name()?;

                        // Parse optional generic type arguments: method<T, U>(...)
                        let generic_args = self.try_parse_method_generic_args();

                        if self.check(&TokenKind::LParen) {
                            let mut args = self.parse_arguments()?;
                            let method_callee = Expr::Identifier(field.clone());
                            self.transform_placeholder_args_for_call(&method_callee, &mut args);
                            // Check for trailing block: obj.method(args) \x: body
                            if self.check(&TokenKind::Backslash) {
                                let trailing_lambda = self.parse_trailing_lambda()?;
                                args.push(Argument::new(None, trailing_lambda));
                            }
                            // Parsing cannot distinguish an ALL_CAPS constant
                            // receiver from an acronym type such as `TCB`.
                            // Preserve the receiver uniformly; HIR/interpreter
                            // resolution owns the value-versus-type decision.
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args,
                                generic_args,
                            };
                        } else if self.check(&TokenKind::Backslash) {
                            // Method call with only trailing block: obj.method \x: body
                            let trailing_lambda = self.parse_trailing_lambda()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument::new(None, trailing_lambda)],
                                generic_args,
                            };
                        } else if self.check(&TokenKind::LBrace)
                            && !self.no_brace_postfix
                            && field.chars().next().is_some_and(|c| c.is_uppercase())
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
                            let mut spread = None;
                            while !self.check(&TokenKind::RBrace) {
                                // Check for spread: ..base_expr
                                if self.check(&TokenKind::DoubleDot) {
                                    self.advance(); // consume '..'
                                    let spread_expr = self.parse_expression()?;
                                    spread = Some(Box::new(spread_expr));
                                    while self.check(&TokenKind::Newline) {
                                        self.advance();
                                    }
                                    if self.check(&TokenKind::Comma) {
                                        self.advance();
                                        while self.check(&TokenKind::Newline) {
                                            self.advance();
                                        }
                                    }
                                    break; // spread must be last
                                }
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
                                spread,
                            };
                        } else if self.check(&TokenKind::LBrace) && !self.no_brace_postfix {
                            // Method call with dict argument: obj.method {...}
                            // Parse the dict as the single argument
                            let dict_expr = self.parse_expression()?;
                            expr = Expr::MethodCall {
                                receiver: Box::new(expr),
                                method: field,
                                args: vec![Argument::new(None, dict_expr)],
                                generic_args,
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
                    // Supports multi-line: expr ??\n    default
                    self.advance();
                    self.binary_indent_count += self.skip_newlines_and_indents_for_method_chain();
                    let default = self.parse_pipe()?;
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
                            let default = self.parse_expression()?;
                            expr = Expr::UnwrapOrReturn {
                                expr: Box::new(expr),
                                default: Box::new(default),
                            };
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
                    let target_type = self.parse_cast_type()?;

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
                TokenKind::At => {
                    // @volatile val: Type / @volatile var: Type
                    // Volatile memory access postfix: addr_expr @volatile val: Type
                    // Peek ahead: next must be identifier "volatile", and token after that must be Val or Var
                    let next = self.peek_next();
                    let is_volatile_access = if let TokenKind::Identifier { name, .. } = &next.kind {
                        if name == "volatile" {
                            // Need to peek 2 ahead: save state, advance twice, check
                            let saved_current = self.current.clone();
                            let saved_previous = self.previous.clone();
                            self.advance(); // consume @
                            self.advance(); // consume "volatile"
                            let is_val_or_var = self.check(&TokenKind::Val) || self.check(&TokenKind::Var);
                            // Restore state
                            self.pending_tokens.push_front(self.current.clone());
                            let volatile_tok = self.previous.clone();
                            self.pending_tokens.push_front(crate::token::Token {
                                kind: TokenKind::Identifier {
                                    name: "volatile".to_string(),
                                    pattern: crate::token::NamePattern::Immutable,
                                },
                                lexeme: "volatile".to_string(),
                                span: volatile_tok.span,
                            });
                            self.current = saved_current;
                            self.previous = saved_previous;
                            is_val_or_var
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if is_volatile_access {
                        // Consume @, "volatile", val/var
                        self.advance(); // consume @
                        self.advance(); // consume "volatile"
                        let mutable = self.check(&TokenKind::Var);
                        self.advance(); // consume val or var
                        self.expect(&TokenKind::Colon)?;
                        let access_type = self.parse_type()?;
                        expr = Expr::VolatileAccess {
                            address: Box::new(expr),
                            mutable,
                            access_type,
                        };
                    } else {
                        break;
                    }
                }
                TokenKind::DoubleColon => {
                    // Handle `Foo<Int>::bar()` where generic args were consumed above and
                    // `expr` is still `Identifier("Foo")`.  Build a Path from the segments
                    // exactly like `parse_identifier_or_struct` does for bare `Foo::bar`.
                    // Emit the same deprecation hint that the primary path already emits for
                    // plain `Foo::bar`, so the behaviour is consistent.
                    if let Expr::Identifier(ref base) = expr.clone() {
                        use crate::error_recovery::{ErrorHint, ErrorHintLevel};
                        let colon_span = self.current.span;
                        let warning = ErrorHint {
                            level: ErrorHintLevel::Warning,
                            message: "Deprecated syntax for static method/variant access".to_string(),
                            span: colon_span,
                            suggestion: Some("Use dot syntax (.) instead of double colon (::)".to_string()),
                            help: Some("Example: Type.new() instead of Type::new()".to_string()),
                        };
                        self.error_hints.push(warning);

                        let mut segments = vec![base.clone()];
                        while self.check(&TokenKind::DoubleColon) {
                            self.advance(); // consume '::'

                            // Skip turbofish ::<T> if present (already deprecated)
                            if self.check(&TokenKind::Lt) {
                                self.advance(); // consume '<'
                                let mut depth = 1u32;
                                while depth > 0 && !self.is_at_end() {
                                    match &self.current.kind {
                                        TokenKind::Lt => {
                                            depth += 1;
                                            self.advance();
                                        }
                                        TokenKind::Gt => {
                                            depth -= 1;
                                            self.advance();
                                        }
                                        TokenKind::ShiftRight => {
                                            if depth >= 2 {
                                                depth -= 2;
                                            } else {
                                                depth = 0;
                                            }
                                            self.advance();
                                        }
                                        _ => {
                                            self.advance();
                                        }
                                    }
                                }
                                break;
                            }

                            let segment = self.expect_method_name()?;
                            segments.push(segment);
                        }
                        expr = Expr::Path(segments);
                    } else {
                        break;
                    }
                }
                TokenKind::Newline => {
                    // Multi-line method chaining: obj.method()\n    .another()
                    // Check if a dot follows after newlines/indents
                    if self.peek_through_newlines_and_indents_is(&TokenKind::Dot) {
                        consumed_indents += self.skip_newlines_and_indents_for_method_chain();
                        // Now self.current should be Dot, continue the loop
                    } else if matches!(
                        self.peek_indented_operator_continuation(),
                        Some(TokenKind::DoubleQuestion)
                    ) {
                        // Leading-operator line continuation for `??`
                        // (`a\n    ?? b`). The trailing form (`a ??\n  b`) was
                        // already handled in the `DoubleQuestion` arm above;
                        // the leading form was the last member of the
                        // comparison/equality family the seed still rejected
                        // while the self-hosted parser accepted it. See
                        // doc/08_tracking/bug/
                        // parser_leading_operator_line_continuation_2026-08-01.md
                        // and `skip_leading_comparison_continuation` in
                        // expressions/binary.rs for why the continuation must
                        // sit on a STRICTLY more deeply indented line.
                        consumed_indents += self.skip_newlines_and_indents_for_method_chain();
                        // Now self.current should be DoubleQuestion; loop.
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

    /// True when `e` is spelled like a TYPE in element position of an array
    /// literal that is immediately called: a bare name (`i64`, `Point`) or a
    /// nested array type (`[i64]`). See `is_typed_empty_array_ctor`.
    fn is_array_element_type_expr(e: &Expr) -> bool {
        match e {
            Expr::Identifier(_) => true,
            Expr::Array(elems) => elems.len() == 1 && Self::is_array_element_type_expr(&elems[0]),
            _ => false,
        }
    }

    /// `[T]()` is the typed empty-array constructor, e.g. `val a: [i64] = [i64]()`.
    ///
    /// Without this, `[i64]` parses as an ordinary array literal whose element
    /// `i64` is then resolved as a VARIABLE, and the whole thing is CALLED --
    /// which failed everywhere with `variable \`i64\` not found` (interpreter)
    /// or `GlobalLoad: unresolved identifier 'i64'` (JIT). Recognising the form
    /// here, in the parser, fixes every downstream lane at once.
    ///
    /// Only a ZERO-argument call on a SINGLE-element array literal whose element
    /// is spelled like a type is intercepted; calling an array value is not a
    /// legal operation in any other spelling, so nothing valid is swallowed.
    /// doc/08_tracking/bug/typed_empty_array_constructor_rejected_2026-08-10.md
    fn is_typed_empty_array_ctor(callee: &Expr, args: &[Argument]) -> bool {
        if !args.is_empty() {
            return false;
        }
        match callee {
            Expr::Array(elems) => elems.len() == 1 && Self::is_array_element_type_expr(&elems[0]),
            _ => false,
        }
    }

    pub(crate) fn parse_call(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mut args = self.parse_arguments()?;
        if !self.check(&TokenKind::Backslash) && Self::is_typed_empty_array_ctor(&callee, &args) {
            return Ok(Expr::Array(Vec::new()));
        }
        self.transform_placeholder_args_for_call(&callee, &mut args);
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

    /// Parse CUDA kernel launch: kernel<<<grid: expr, block: expr>>>(args)
    /// The `<<<` token has already been seen as the current token.
    fn parse_kernel_launch(&mut self, kernel: Expr) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::TripleLt)?; // consume <<<

        // Parse grid expression: "grid:" expr
        // Accept both named (grid: expr) and positional (expr, expr) forms
        // Note: "grid" is a keyword (TokenKind::Grid), not an identifier
        let grid = if self.check(&TokenKind::Grid) {
            self.advance(); // consume "grid"
            self.expect(&TokenKind::Colon)?;
            self.parse_expression()?
        } else {
            self.parse_expression()?
        };

        self.expect(&TokenKind::Comma)?;

        // Parse block expression: "block:" expr
        // "block" is a regular identifier (not a keyword)
        let block = if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "block") {
            self.advance(); // consume "block"
            self.expect(&TokenKind::Colon)?;
            self.parse_expression()?
        } else {
            self.parse_expression()?
        };

        self.expect(&TokenKind::TripleGt)?; // consume >>>

        // Parse the call arguments: (args)
        let args = self.parse_arguments()?;

        Ok(Expr::KernelLaunch {
            kernel: Box::new(kernel),
            grid: Box::new(grid),
            block: Box::new(block),
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
        // Check for destructuring lambda: \(name, pattern):
        // Treat (ident, ident, ...) as individual lambda parameters
        else if self.check(&TokenKind::LParen) {
            self.advance(); // consume '('
            while !self.check(&TokenKind::RParen) && !self.is_at_end() {
                let param_span = self.current.span;
                let name = if self.check(&TokenKind::Underscore) {
                    self.advance();
                    "_".to_string()
                } else {
                    self.expect_identifier()?
                };
                if Self::is_reserved_parameter_name(name.as_str()) {
                    return Err(ParseError::syntax_error_with_span(
                        format!("reserved keyword '{}' cannot be used as a parameter name", name),
                        param_span,
                    ));
                }
                params.push(LambdaParam { name, ty: None });
                if self.check(&TokenKind::Comma) {
                    self.advance();
                }
            }
            self.expect(&TokenKind::RParen)?;
        }
        // Check for no-param lambda: \: expr (also treated as capture-all)
        else if !self.check(&TokenKind::Colon) {
            // Check for wildcard parameter: \_
            let param_span = self.current.span;
            let name = if self.check(&TokenKind::Underscore) {
                self.advance();
                "_".to_string()
            } else {
                self.expect_identifier()?
            };
            if Self::is_reserved_parameter_name(name.as_str()) {
                return Err(ParseError::syntax_error_with_span(
                    format!("reserved keyword '{}' cannot be used as a parameter name", name),
                    param_span,
                ));
            }
            params.push(LambdaParam { name, ty: None });
            self.parse_remaining_lambda_params(&mut params, false)?;
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
            let param_span = self.current.span;
            let name = if self.check(&TokenKind::Underscore) {
                self.advance();
                "_".to_string()
            } else {
                self.expect_identifier()?
            };
            if Self::is_reserved_parameter_name(name.as_str()) {
                return Err(ParseError::syntax_error_with_span(
                    format!("reserved keyword '{}' cannot be used as a parameter name", name),
                    param_span,
                ));
            }
            let ty = if self.check(&TokenKind::Colon) {
                self.advance();
                // Use parse_single_type, not parse_type: parse_type continues
                // through `|` to build a union type, which would swallow the
                // pipe-lambda's own closing `|`.
                Some(self.parse_single_type()?)
            } else {
                None
            };
            params.push(LambdaParam { name, ty });
            self.parse_remaining_lambda_params(&mut params, true)?;
        }
        Ok(params)
    }

    /// Try to parse generic type arguments on a method call: `method<T, U>(...)`.
    ///
    /// The `<` token is ambiguous — it could be a generic arg list or a less-than comparison.
    /// We use speculative parsing: save the parser state, try to parse as generic args
    /// (comma-separated types ending with `>` followed by `(`), and backtrack if it fails.
    ///
    /// Returns the parsed generic args, or an empty vec if this is not a generic arg list.
    fn try_parse_method_generic_args(&mut self) -> Vec<Type> {
        if !self.check(&TokenKind::Lt) {
            return Vec::new();
        }

        // Save parser state for backtracking
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_tokens.clone();
        let saved_lexer = self.lexer.clone();
        // `parse_type` below PUSHES diagnostics (notably the `name[...]`
        // deprecated-generics warning) as a side effect. Token state is
        // restored on backtrack but `error_hints` is not, so a speculative
        // parse that is later abandoned still leaks its warnings. Record the
        // watermark and truncate back to it when we backtrack.
        let saved_hints_len = self.error_hints.len();

        // Try to parse generic args
        self.advance(); // consume '<'

        let mut args = Vec::new();
        let mut succeeded = false;

        // Try to parse comma-separated type arguments
        loop {
            // Handle >> token splitting for nested generics like method<List<T>>()
            if self.check(&TokenKind::ShiftRight) {
                // Split >> into two > tokens
                let shift_span = self.current.span;
                use crate::token::{Span, Token};

                let first_gt = Token::new(
                    TokenKind::Gt,
                    Span::new(
                        shift_span.start,
                        shift_span.start + 1,
                        shift_span.line,
                        shift_span.column,
                    ),
                    ">".to_string(),
                );
                let second_gt = Token::new(
                    TokenKind::Gt,
                    Span::new(
                        shift_span.start + 1,
                        shift_span.end,
                        shift_span.line,
                        shift_span.column + 1,
                    ),
                    ">".to_string(),
                );

                self.current = first_gt;
                self.pending_tokens.push_front(second_gt);
            }

            if self.check(&TokenKind::Gt) {
                // End of generic args — check that `(` follows
                self.advance(); // consume '>'
                if self.check(&TokenKind::LParen) || self.check(&TokenKind::Backslash) || self.check(&TokenKind::LBrace)
                {
                    succeeded = true;
                }
                break;
            }

            // Try to parse a type
            match self.parse_type() {
                Ok(ty) => args.push(ty),
                Err(_) => break, // Not a valid type — this is not a generic arg list
            }

            // Expect comma or closing >
            if self.check(&TokenKind::Comma) {
                self.advance(); // consume ','
            } else if !self.check(&TokenKind::Gt) && !self.check(&TokenKind::ShiftRight) {
                break; // Neither comma nor > — not a generic arg list
            }
        }

        if succeeded && !args.is_empty() {
            args
        } else {
            // Backtrack: restore parser state
            self.current = saved_current;
            self.previous = saved_previous;
            self.pending_tokens = saved_pending;
            self.lexer = saved_lexer;
            self.error_hints.truncate(saved_hints_len);
            Vec::new()
        }
    }

    /// Lookahead for `Foo<Int>.bar()`, `Foo<Int>::bar()`, and `Foo<Int> { ... }`.
    ///
    /// Called when the just-parsed primary is a bare `Identifier` and the current token is `<`.
    /// Speculatively consumes `<TypeArgs>` (using `parse_type` for each arg, with `>>` splitting).
    /// **Commits** (leaves the parser after the `>`) only if a postfix or enabled struct
    /// literal follows — clear evidence that `<...>` is a type-argument list, not a comparison.
    /// **Backtracks** otherwise, leaving `<` as `TokenKind::Lt` for the binary-expression layer.
    ///
    /// The parsed type args are discarded in the seed; the caller's `expr` (Identifier) is
    /// unchanged so that the postfix loop can continue with `.bar()` or `::bar()`.
    pub(super) fn try_skip_ident_generic_args(&mut self) -> Result<(), ParseError> {
        // Save state for backtracking
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_tokens.clone();
        let saved_lexer = self.lexer.clone();
        // See try_parse_method_generic_args: `parse_type` pushes diagnostics as
        // a side effect, and backtracking restored only token state. For
        // `a < arr[i]` this leaked a bogus "Use angle brackets: arr<...>"
        // deprecation warning even though the speculative type parse was
        // correctly abandoned and the comparison parsed fine.
        // See doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md
        let saved_hints_len = self.error_hints.len();

        self.advance(); // consume '<'

        let mut depth: u32 = 1;
        let mut ok = false;
        // A numeric literal in generic-argument position is a CONST GENERIC
        // argument (`Tensor<i64, 2>`). Simple has no const generic parameters,
        // so it is not a type and `parse_type` rejects it. Without this flag the
        // whole list silently backtracks into a comparison chain and dies later
        // on the `,` with "expected expression, found Comma" — a diagnostic that
        // names neither the construct nor the limitation. Record the span so a
        // confirmed generic-argument shape (`... > (`) can be reported exactly.
        // See doc/08_tracking/bug/const_generic_argument_rejected_in_constructor_call_2026-08-17.md
        let mut const_arg_span: Option<crate::token::Span> = None;
        // A real generic-argument list is `T (, T)*`: two arguments can never sit
        // side by side without a separating comma. Comparison chains routinely
        // produce that shape (`a < 0 or a > (b)` scans as `0`, `or`, `a` — three
        // "arguments", no commas) and `parse_type` happily accepts a bare keyword
        // or identifier as a named type, so without this ratchet the scan reaches
        // `>` followed by `(`, declares the shape confirmed and hard-errors on the
        // recorded const-generic span instead of backtracking into the comparison.
        // See doc/08_tracking/bug/parser_comparison_chain_misread_as_generic_args_2026-08-18.md
        let mut need_comma = false;

        // Consume the generic arg list, tracking nesting depth to handle `Foo<Bar<T>>`.
        // We use `parse_type` calls (with backtrack-on-error) to validate the contents —
        // if any token inside cannot start a type we abort immediately.
        loop {
            // Handle >> as two >
            if self.check(&TokenKind::ShiftRight) {
                if depth >= 2 {
                    depth -= 2;
                    self.advance();
                    if depth == 0 {
                        // After closing all nested levels, check if continuation follows
                        ok = self.check(&TokenKind::Dot)
                            || self.check(&TokenKind::DoubleColon)
                            || self.check(&TokenKind::LParen)
                            || (!self.no_brace_postfix && self.check(&TokenKind::LBrace));
                        break;
                    }
                    continue;
                } else {
                    // depth == 1: >> closes the outer and yields a stray >
                    // Split: consume one > and push the other back
                    let shift_span = self.current.span;
                    use crate::token::{Span, Token};
                    let second_gt = Token::new(
                        TokenKind::Gt,
                        Span::new(
                            shift_span.start + 1,
                            shift_span.end,
                            shift_span.line,
                            shift_span.column + 1,
                        ),
                        ">".to_string(),
                    );
                    self.current = Token::new(
                        TokenKind::Gt,
                        Span::new(
                            shift_span.start,
                            shift_span.start + 1,
                            shift_span.line,
                            shift_span.column,
                        ),
                        ">".to_string(),
                    );
                    self.pending_tokens.push_front(second_gt);
                    // fall through to Gt handling below
                }
            }

            if self.check(&TokenKind::Gt) {
                depth -= 1;
                self.advance();
                if depth == 0 {
                    ok = self.check(&TokenKind::Dot)
                        || self.check(&TokenKind::DoubleColon)
                        || self.check(&TokenKind::LParen)
                        || (!self.no_brace_postfix && self.check(&TokenKind::LBrace));
                    break;
                }
                need_comma = true;
                continue;
            }

            if self.check(&TokenKind::Lt) {
                depth += 1;
                self.advance();
                need_comma = false;
                continue;
            }

            if self.is_at_end() {
                break;
            }

            // A bare integer literal here is a const-generic argument. Consume it
            // like a type arg so the list can still reach its closing `>`; the
            // recorded span turns into a precise diagnostic below once the shape
            // is confirmed to be a generic argument list and not a comparison.
            if matches!(self.current.kind, TokenKind::Integer(_) | TokenKind::TypedInteger(_, _)) {
                if need_comma {
                    break;
                }
                if const_arg_span.is_none() {
                    const_arg_span = Some(self.current.span);
                }
                self.advance();
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    need_comma = false;
                } else {
                    need_comma = true;
                }
                continue;
            }

            // A separator between arguments. Reached when the previous argument
            // ended at a closing `>` of a nested list (the `Gt` branch above
            // `continue`s without consuming what follows), which `parse_type`
            // cannot start on.
            if self.check(&TokenKind::Comma) {
                self.advance();
                need_comma = false;
                continue;
            }

            // `Ident <` opens a NESTED generic argument list. Step over the name
            // only and let this loop's own `Lt`/`Gt`/`Comma` branches walk the
            // nesting, instead of handing the whole thing to `parse_type`.
            // `parse_type` would swallow the inner list and then fail on an inner
            // const-generic argument (`Box2<Box2<i64, 4>, i32>`), losing both the
            // depth bookkeeping and the const-argument span.
            if matches!(self.current.kind, TokenKind::Identifier { .. }) && self.peek_is(&TokenKind::Lt) {
                if need_comma {
                    break;
                }
                self.advance();
                continue;
            }

            if need_comma {
                break;
            }

            // Try to parse a type arg; if that fails this is not a valid generic list
            match self.parse_type() {
                Ok(_) => {}
                Err(_) => break,
            }

            // After a type arg expect comma or closing >
            if self.check(&TokenKind::Comma) {
                self.advance();
                need_comma = false;
            } else {
                need_comma = true;
            }
            // continue loop — next iteration checks for > or more types
        }

        if !ok {
            // Backtrack: this was a comparison, not a generic arg list
            self.current = saved_current;
            self.previous = saved_previous;
            self.pending_tokens = saved_pending;
            self.lexer = saved_lexer;
            self.error_hints.truncate(saved_hints_len);
            return Ok(());
        }
        // The shape is confirmed: a closed `<...>` followed by `(`, `.`, `::` or
        // `{`. If one of the arguments was a numeric literal, this is a const
        // generic argument, which the language does not have. Say so, instead of
        // backtracking into a comparison and blaming a later comma.
        if let Some(span) = const_arg_span {
            return Err(ParseError::unexpected_token(
                "a type in generic argument position (Simple has no const generic parameters, so a \
                 numeric literal such as `Tensor<i64, 2>` is not a valid generic argument; drop the \
                 explicit generic arguments and let them be inferred, e.g. `Tensor(...)`)",
                "integer literal".to_string(),
                span,
            ));
        }
        // Otherwise the generic args were consumed and discarded; caller's expr is unchanged.
        Ok(())
    }
}

/// Re-split a lexer-munched `digits.digits` float lexeme back into the two
/// tuple indices it actually was: `r.0.1` lexes `0.1` as one Float token.
///
/// seed_nested_tuple_index_float_munch_2026-08-06.
///
/// Returns `None` for anything that is not EXACTLY `digits '.' digits`, so a
/// genuine float lexeme (`1e3`, `0.1f32`, `1_0.5`, `.5`, `1.`) is never
/// silently reinterpreted as a tuple path. Works on the LEXEME rather than the
/// parsed `f64` on purpose: `.0.10` and `.0.1` share the value `0.1`, and
/// binary floating point cannot represent most decimal lexemes exactly, so the
/// value is not a usable index source.
fn split_tuple_index_pair(lexeme: &str) -> Option<(usize, usize)> {
    let (lhs, rhs) = lexeme.split_once('.')?;
    // A second '.' means this was never a simple pair.
    if rhs.contains('.') {
        return None;
    }
    // Reject empty halves (`.5`, `1.`) and any non-ASCII-digit character, which
    // covers signs, exponents (`1e3`), `_` separators, and numeric suffixes
    // (`0.1f32` arrives as TypedFloat, but be defensive).
    if lhs.is_empty()
        || rhs.is_empty()
        || !lhs.bytes().all(|b| b.is_ascii_digit())
        || !rhs.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    Some((lhs.parse().ok()?, rhs.parse().ok()?))
}

#[cfg(test)]
mod tuple_index_split_tests {
    use super::split_tuple_index_pair;

    #[test]
    fn splits_a_plain_digit_dot_digit_lexeme() {
        assert_eq!(split_tuple_index_pair("0.1"), Some((0, 1)));
        assert_eq!(split_tuple_index_pair("1.0"), Some((1, 0)));
        assert_eq!(split_tuple_index_pair("12.34"), Some((12, 34)));
        // Leading zeros are still just digits: `.0.01` is index 0 then index 1.
        assert_eq!(split_tuple_index_pair("0.01"), Some((0, 1)));
    }

    /// The whole reason this works on text: these two lexemes have the SAME
    /// f64 value but different tuple paths, so an f64-based implementation
    /// would be wrong.
    #[test]
    fn distinguishes_lexemes_that_share_an_f64_value() {
        assert_eq!(split_tuple_index_pair("0.1"), Some((0, 1)));
        assert_eq!(split_tuple_index_pair("0.10"), Some((0, 10)));
    }

    #[test]
    fn refuses_anything_that_is_not_digits_dot_digits() {
        for bad in [
            "1e3", "1.5e3", "0.1f32", "1_0.5", "0.5_0", ".5", "1.", "1.2.3", "-1.2", "+1.2", "0x1.8", "", ".", "a.b",
            "1.2i64",
        ] {
            assert_eq!(split_tuple_index_pair(bad), None, "must refuse {bad:?}");
        }
    }
}
