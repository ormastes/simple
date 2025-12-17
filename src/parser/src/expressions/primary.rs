// Primary expression parsing - extracted from mod.rs for maintainability

impl<'a> Parser<'a> {
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
            TokenKind::TypedString(s, suffix) => {
                // String with unit suffix: "127.0.0.1"_ip
                let s = s.clone();
                let suffix = suffix.clone();
                self.advance();
                Ok(Expr::TypedString(s, suffix))
            }
            TokenKind::TypedRawString(s, suffix) => {
                // Raw string with unit suffix: '127.0.0.1'_ip
                let s = s.clone();
                let suffix = suffix.clone();
                self.advance();
                Ok(Expr::TypedString(s, suffix))
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
            // Contract special expressions
            TokenKind::Old => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let expr = self.parse_expression()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Expr::ContractOld(Box::new(expr)))
            }
            TokenKind::Result => {
                // Allow 'result' as a regular identifier (like 'type', 'out', etc.)
                // ContractResult expression is only generated in contract blocks
                self.advance();
                Ok(Expr::Identifier("result".to_string()))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();
                // Check for path expression: Name::Variant
                if self.check(&TokenKind::DoubleColon) {
                    let mut segments = vec![name];
                    while self.check(&TokenKind::DoubleColon) {
                        self.advance(); // consume '::'
                        // Use expect_method_name to allow keywords like 'new', 'type', etc.
                        let segment = self.expect_method_name()?;
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
            // Allow certain keywords to be used as identifiers in expressions
            TokenKind::Out => {
                self.advance();
                Ok(Expr::Identifier("out".to_string()))
            }
            TokenKind::OutErr => {
                self.advance();
                Ok(Expr::Identifier("out_err".to_string()))
            }
            TokenKind::Type => {
                self.advance();
                Ok(Expr::Identifier("type".to_string()))
            }
            // Note: TokenKind::Result is handled above (line 96) for ContractResult
            // If needed as identifier, use method_name or a different syntax
            TokenKind::Backslash => {
                // Lambda: \x: expr or \x, y: expr or \: expr
                self.advance();
                self.parse_lambda_body(MoveMode::Copy)
            }
            TokenKind::Pipe => {
                // Lambda: |x| body or |x, y| body (Ruby/Rust style)
                self.advance();
                let params = self.parse_pipe_lambda_params()?;
                self.expect(&TokenKind::Pipe)?;
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
                if !self.check(&TokenKind::Backslash) {
                    return Err(ParseError::unexpected_token(
                        "'\\'",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
                self.advance();
                self.parse_lambda_body(MoveMode::Move)
            }
            TokenKind::LParen => {
                self.advance();
                // Skip whitespace tokens inside parens (for multi-line expressions)
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }
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

                // Skip whitespace before checking what comes next
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }

                if self.check(&TokenKind::Comma) {
                    // Tuple
                    let mut elements = vec![first];
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        // Skip whitespace after comma
                        while self.check(&TokenKind::Newline)
                            || self.check(&TokenKind::Indent)
                            || self.check(&TokenKind::Dedent)
                        {
                            self.advance();
                        }
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        elements.push(self.parse_expression()?);
                        // Skip whitespace after element
                        while self.check(&TokenKind::Newline)
                            || self.check(&TokenKind::Indent)
                            || self.check(&TokenKind::Dedent)
                        {
                            self.advance();
                        }
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
                // Skip whitespace tokens inside brackets (for multi-line arrays)
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }
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

                // Skip whitespace after first element
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }

                // Check for list comprehension: [expr for pattern in iterable]
                if self.check(&TokenKind::For) {
                    self.advance();
                    let (pattern, iterable, condition) = self.parse_comprehension_clause()?;
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
                    // Skip whitespace after comma
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                    {
                        self.advance();
                    }
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
                    // Skip whitespace after element
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                    {
                        self.advance();
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
                    let (pattern, iterable, condition) = self.parse_comprehension_clause()?;
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
            TokenKind::If | TokenKind::Elif => {
                self.advance();
                self.parse_if_expr()
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
            // Handle vec keyword: vec! macro, vec[...] literal, or identifier
            TokenKind::Vec => {
                self.advance();
                // If followed by !, it's a macro invocation
                if self.check(&TokenKind::Bang) {
                    self.advance(); // consume !
                    let args = self.parse_macro_args()?;
                    Ok(Expr::MacroInvocation {
                        name: "vec".to_string(),
                        args,
                    })
                } else if self.check(&TokenKind::LBracket) {
                    // SIMD vector literal: vec[1.0, 2.0, 3.0, 4.0]
                    self.advance(); // consume '['

                    // Skip whitespace
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                    {
                        self.advance();
                    }

                    // Empty vector
                    if self.check(&TokenKind::RBracket) {
                        self.advance();
                        return Ok(Expr::VecLiteral(Vec::new()));
                    }

                    // Parse elements
                    let mut elements = Vec::new();
                    elements.push(self.parse_expression()?);

                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        // Skip whitespace after comma
                        while self.check(&TokenKind::Newline)
                            || self.check(&TokenKind::Indent)
                            || self.check(&TokenKind::Dedent)
                        {
                            self.advance();
                        }
                        if self.check(&TokenKind::RBracket) {
                            break;
                        }
                        elements.push(self.parse_expression()?);
                    }
                    self.expect(&TokenKind::RBracket)?;
                    Ok(Expr::VecLiteral(elements))
                } else {
                    // Otherwise return as an identifier (for backward compatibility)
                    Ok(Expr::Identifier("vec".to_string()))
                }
            }
            // Handle gpu keyword as an identifier for gpu.* intrinsic function calls
            TokenKind::Gpu => {
                self.advance();
                Ok(Expr::Identifier("gpu".to_string()))
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
