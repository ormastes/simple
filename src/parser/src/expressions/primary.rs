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

                        // Check for shorthand syntax: { x, y } instead of { x: x, y: y }
                        let value = if self.check(&TokenKind::Colon) {
                            // Explicit value: field: value
                            self.advance(); // consume ':'
                            // Skip newlines after colon
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            self.parse_expression()?
                        } else {
                            // Shorthand: field means field: field
                            Expr::Identifier(field_name.clone())
                        };

                        // Skip newlines after value
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        fields.push((field_name, value));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                            // Skip newlines after comma
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
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
            // Allow Gherkin keywords to be used as identifiers in expressions
            TokenKind::Feature => {
                self.advance();
                Ok(Expr::Identifier("feature".to_string()))
            }
            TokenKind::Scenario => {
                self.advance();
                Ok(Expr::Identifier("scenario".to_string()))
            }
            TokenKind::Outline => {
                self.advance();
                Ok(Expr::Identifier("outline".to_string()))
            }
            TokenKind::Examples => {
                self.advance();
                Ok(Expr::Identifier("examples".to_string()))
            }
            TokenKind::Given => {
                self.advance();
                Ok(Expr::Identifier("given".to_string()))
            }
            TokenKind::When => {
                self.advance();
                Ok(Expr::Identifier("when".to_string()))
            }
            TokenKind::Then => {
                self.advance();
                Ok(Expr::Identifier("then".to_string()))
            }
            TokenKind::AndThen => {
                self.advance();
                Ok(Expr::Identifier("and_then".to_string()))
            }
            // Allow 'context' to be used as identifier in BDD DSL (context "description":)
            TokenKind::Context => {
                self.advance();
                Ok(Expr::Identifier("context".to_string()))
            }
            // Allow 'common' to be used as identifier (stdlib directory name)
            TokenKind::Common => {
                self.advance();
                Ok(Expr::Identifier("common".to_string()))
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
                // Skip newlines after opening brace
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }

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
                // Skip newlines before colon
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                self.expect(&TokenKind::Colon)?;
                // Skip newlines after colon
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                let value = self.parse_expression()?;
                // Skip newlines after value
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }

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
                    // Skip newlines after comma
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
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
                        // Skip newlines before colon
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        self.expect(&TokenKind::Colon)?;
                        // Skip newlines after colon
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        let v = self.parse_expression()?;
                        // Skip newlines after value
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
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
            // Allow BDD/Gherkin keywords as identifiers in expressions
            TokenKind::Context => {
                self.advance();
                Ok(Expr::Identifier("context".to_string()))
            }
            TokenKind::Feature => {
                self.advance();
                Ok(Expr::Identifier("feature".to_string()))
            }
            TokenKind::Scenario => {
                self.advance();
                Ok(Expr::Identifier("scenario".to_string()))
            }
            TokenKind::Given => {
                self.advance();
                Ok(Expr::Identifier("given".to_string()))
            }
            TokenKind::When => {
                self.advance();
                Ok(Expr::Identifier("when".to_string()))
            }
            TokenKind::Then => {
                self.advance();
                Ok(Expr::Identifier("then".to_string()))
            }
            // Allow 'common' as identifier (stdlib directory name)
            TokenKind::Common => {
                self.advance();
                Ok(Expr::Identifier("common".to_string()))
            }
            // Simple Math: Grid literal (#1910-#1919)
            TokenKind::Grid => self.parse_grid_literal(),
            // Simple Math: Tensor literal (#1910-#1919)
            TokenKind::Tensor => self.parse_tensor_literal(),
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
        // Accept both -> and => for match arms
        if !self.check(&TokenKind::Arrow) && !self.check(&TokenKind::FatArrow) {
            return Err(ParseError::unexpected_token(
                "-> or =>",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }
        self.advance();
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

    // ========================================================================
    // Simple Math: Grid/Tensor Literal Parsing (#1910-#1919)
    // ========================================================================

    /// Parse grid literal: grid device="cuda": | row | row |
    fn parse_grid_literal(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'grid'

        // Optional device parameter: grid device="cuda":
        let device = if self.check_ident("device") {
            self.advance(); // consume 'device'
            self.expect(&TokenKind::Assign)?;
            match &self.current.kind {
                TokenKind::String(s) => {
                    let dev = s.clone();
                    self.advance();
                    Some(dev)
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "string literal for device",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let rows = self.parse_grid_rows()?;

        self.expect(&TokenKind::Dedent)?;

        // Box all expressions in rows
        let boxed_rows = rows
            .into_iter()
            .map(|row| row.into_iter().map(Box::new).collect())
            .collect();

        Ok(Expr::GridLiteral {
            rows: boxed_rows,
            device,
        })
    }

    /// Parse grid rows: | cell | cell | ...
    fn parse_grid_rows(&mut self) -> Result<Vec<Vec<Expr>>, ParseError> {
        let mut rows = Vec::new();

        while self.check(&TokenKind::Pipe) {
            self.advance(); // consume leading |

            let mut cells = Vec::new();
            loop {
                // Parse cell expression
                let cell = self.parse_expression()?;
                cells.push(cell);

                if self.check(&TokenKind::Pipe) {
                    self.advance(); // consume |
                    // Check if this is the trailing | (end of row)
                    if self.check(&TokenKind::Newline) {
                        break;
                    }
                } else {
                    return Err(ParseError::missing_token("| after grid cell", self.current.span));
                }
            }

            self.expect(&TokenKind::Newline)?;
            rows.push(cells);

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if rows.is_empty() {
            return Err(ParseError::syntax_error_with_span(
                "Grid literal must have at least one row",
                self.current.span,
            ));
        }

        Ok(rows)
    }

    /// Parse tensor literal: tensor K: Float [d=2, h=3] ...
    fn parse_tensor_literal(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'tensor'

        // Parse name: K
        let _name = if let TokenKind::Identifier(name) = &self.current.kind.clone() {
            let n = name.clone();
            self.advance();
            n
        } else {
            return Err(ParseError::unexpected_token(
                "identifier for tensor name",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Colon)?;

        // Parse dtype: Float, Int, etc.
        let dtype = if let TokenKind::Identifier(dt) = &self.current.kind.clone() {
            let d = dt.clone();
            self.advance();
            d
        } else {
            return Err(ParseError::unexpected_token(
                "type name for tensor",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Parse dimensions: [d=2, h=3, w=4]
        self.expect(&TokenKind::LBracket)?;
        let mut dims = Vec::new();
        loop {
            if self.check(&TokenKind::RBracket) {
                break;
            }

            // Parse dim_name=value
            let dim_name = if let TokenKind::Identifier(name) = &self.current.kind.clone() {
                let n = name.clone();
                self.advance();
                n
            } else {
                return Err(ParseError::unexpected_token(
                    "dimension name",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Assign)?;

            let dim_value = if let TokenKind::Integer(val) = self.current.kind {
                self.advance();
                val
            } else {
                return Err(ParseError::unexpected_token(
                    "integer for dimension size",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            dims.push((dim_name, dim_value));

            if self.check(&TokenKind::Comma) {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;

        // Optional device parameter
        let device = if self.check_ident("device") {
            self.advance(); // consume 'device'
            self.expect(&TokenKind::Assign)?;
            match &self.current.kind {
                TokenKind::String(s) => {
                    let dev = s.clone();
                    self.advance();
                    Some(dev)
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "string literal for device",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        } else {
            None
        };

        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse mode: slice or flat
        let mode = if self.check_ident("slice") {
            // Slice mode
            let slices = self.parse_tensor_slices()?;
            TensorMode::Slice(slices)
        } else if self.check_ident("default") || self.check_ident("flat") {
            // Flat mode
            let default_val = if self.check_ident("default") {
                self.advance(); // consume 'default'
                self.expect(&TokenKind::Colon)?;
                let val = self.parse_expression()?;
                self.expect(&TokenKind::Newline)?;
                Some(val)
            } else {
                None
            };

            self.expect(&TokenKind::Flat)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            let values = self.parse_grid_rows()?;

            self.expect(&TokenKind::Dedent)?;

            // Box all expressions in values and default
            let boxed_values = values
                .into_iter()
                .map(|row| row.into_iter().map(Box::new).collect())
                .collect();
            let boxed_default = default_val.map(Box::new);

            TensorMode::Flat {
                default: boxed_default,
                values: boxed_values,
            }
        } else {
            return Err(ParseError::syntax_error_with_span(
                "'slice' or 'flat' mode in tensor literal",
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Dedent)?;

        Ok(Expr::TensorLiteral {
            dtype,
            dims,
            mode: Box::new(mode),
            device,
        })
    }

    /// Parse tensor slices recursively
    fn parse_tensor_slices(&mut self) -> Result<Vec<TensorSlice>, ParseError> {
        use crate::ast::{TensorSlice, TensorSliceContent};

        let mut slices = Vec::new();

        while self.check_ident("slice") {
            self.advance(); // consume 'slice'

            // Parse dim_name=value
            let dim_name = if let TokenKind::Identifier(name) = &self.current.kind.clone() {
                let n = name.clone();
                self.advance();
                n
            } else {
                return Err(ParseError::unexpected_token(
                    "dimension name",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Assign)?;

            let dim_value = if let TokenKind::Integer(val) = self.current.kind {
                self.advance();
                val
            } else {
                return Err(ParseError::unexpected_token(
                    "integer for slice index",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };

            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            // Check if nested slices or grid rows
            let content = if self.check_ident("slice") {
                let nested = self.parse_tensor_slices()?;
                TensorSliceContent::NestedSlices(nested)
            } else {
                let rows = self.parse_grid_rows()?;
                // Box all expressions in grid rows
                let boxed_rows = rows
                    .into_iter()
                    .map(|row| row.into_iter().map(Box::new).collect())
                    .collect();
                TensorSliceContent::GridRows(boxed_rows)
            };

            self.expect(&TokenKind::Dedent)?;

            slices.push(TensorSlice {
                dim_name,
                dim_value,
                content,
            });

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        Ok(slices)
    }
}
