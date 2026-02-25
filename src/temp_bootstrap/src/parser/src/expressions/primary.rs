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
                                Err(_e) => {
                                    // If sub-parser fails, treat the entire interpolation
                                    // as a literal placeholder (e.g., LLVM IR metadata like !{...})
                                    // This allows the file to continue parsing beyond the f-string.
                                    result_parts.push(FStringPart::Literal(
                                        format!("{{{}}}", expr_str),
                                    ));
                                }
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
                // old(...) is a contract expression, but 'old' can also be used as a regular identifier
                if self.check(&TokenKind::LParen) {
                    self.expect(&TokenKind::LParen)?;
                    let expr = self.parse_expression()?;
                    self.expect(&TokenKind::RParen)?;
                    Ok(Expr::ContractOld(Box::new(expr)))
                } else {
                    Ok(Expr::Identifier("old".to_string()))
                }
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
                // Check for `do:` block expression
                if name == "do" && self.check(&TokenKind::Colon) {
                    self.advance(); // consume ':'
                    let block = self.parse_block_or_inline()?;
                    return Ok(Expr::DoBlock(block.statements));
                }
                // Check for path expression: Name::Variant
                if self.check(&TokenKind::DoubleColon) {
                    let mut segments = vec![name];
                    while self.check(&TokenKind::DoubleColon) {
                        self.advance(); // consume '::'
                        // Handle turbofish syntax: name::<T>()
                        if self.check(&TokenKind::Lt) {
                            // Turbofish generic args - parse and skip them
                            self.advance(); // consume '<'
                            let mut depth = 1;
                            while depth > 0 && !self.is_at_end() {
                                if self.check(&TokenKind::Lt) {
                                    depth += 1;
                                } else if self.check(&TokenKind::Gt) {
                                    depth -= 1;
                                    if depth == 0 {
                                        self.advance(); // consume final '>'
                                        break;
                                    }
                                }
                                self.advance();
                            }
                            break;
                        }
                        // Handle destructured path: Name::{a, b, c}
                        if self.check(&TokenKind::LBrace) {
                            self.advance(); // consume '{'
                            self.skip_whitespace_tokens();
                            let mut names = Vec::new();
                            while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                                let name = self.expect_identifier()?;
                                names.push(name);
                                self.skip_whitespace_tokens();
                                if self.check(&TokenKind::Comma) {
                                    self.advance();
                                    self.skip_whitespace_tokens();
                                }
                            }
                            self.expect(&TokenKind::RBrace)?;
                            // Represent as Path with last segment being the group
                            // Just return path with {names} appended as segments
                            for n in names {
                                segments.push(n);
                            }
                            break;
                        }
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
                    // Skip whitespace after opening brace (for multi-line struct inits)
                    self.skip_whitespace_tokens();
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        self.expect(&TokenKind::Colon)?;
                        let value = self.parse_expression()?;
                        fields.push((field_name, value));
                        // Skip whitespace after field value
                        self.skip_whitespace_tokens();
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                            // Skip whitespace after comma
                            self.skip_whitespace_tokens();
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    Ok(Expr::StructInit { name, fields })
                } else if self.check(&TokenKind::LBrace) && (name == "m" || name == "math") {
                    // Math block: m{ expr } or math{ expr }
                    self.advance(); // consume '{'
                    self.skip_whitespace_tokens();
                    let expr = self.parse_expression()?;
                    self.skip_whitespace_tokens();
                    self.expect(&TokenKind::RBrace)?;
                    // Wrap as a call to the math block function
                    Ok(Expr::Call {
                        callee: Box::new(Expr::Identifier(name)),
                        args: vec![Argument { name: None, value: expr }],
                    })
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
                // Also handle \\x: expr (double backslash lambda — treat as single \)
                self.advance();
                // If next token is also a backslash, consume it (\\x means \x)
                if self.check(&TokenKind::Backslash) {
                    self.advance();
                }
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

                // Check for named tuple/struct literal: (name: value, ...)
                // Lookahead: if current is Identifier (or keyword-as-field-name) followed by Colon,
                // parse as named fields
                let is_named_tuple = {
                    let is_name_token = matches!(&self.current.kind,
                        TokenKind::Identifier(_)
                        | TokenKind::Type | TokenKind::Result | TokenKind::Match
                        | TokenKind::From | TokenKind::To | TokenKind::In | TokenKind::As
                        | TokenKind::Context | TokenKind::Out | TokenKind::OutErr | TokenKind::Old
                        | TokenKind::Use | TokenKind::Import | TokenKind::Export
                        | TokenKind::New | TokenKind::Move | TokenKind::Spawn
                        | TokenKind::Shared | TokenKind::Common | TokenKind::Auto
                        | TokenKind::Mut | TokenKind::Pub | TokenKind::Priv
                        | TokenKind::Static | TokenKind::Const | TokenKind::Extern
                        | TokenKind::Vec | TokenKind::Gpu | TokenKind::Dyn
                        | TokenKind::Unit
                    );
                    if is_name_token {
                        let next = self.pending_token.clone()
                            .unwrap_or_else(|| self.lexer.next_token());
                        self.pending_token = Some(next.clone());
                        matches!(next.kind, TokenKind::Colon)
                    } else {
                        false
                    }
                };

                if is_named_tuple {
                    // Parse as named fields: (name: value, name: value, ...)
                    // Field names can be identifiers or keywords (type, result, etc.)
                    let mut fields = Vec::new();
                    loop {
                        // Skip whitespace
                        while self.check(&TokenKind::Newline)
                            || self.check(&TokenKind::Indent)
                            || self.check(&TokenKind::Dedent)
                        {
                            self.advance();
                        }
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        let field_name = self.expect_method_name()?;
                        self.expect(&TokenKind::Colon)?;
                        let value = self.parse_expression()?;
                        fields.push((field_name, value));
                        // Skip whitespace
                        while self.check(&TokenKind::Newline)
                            || self.check(&TokenKind::Indent)
                            || self.check(&TokenKind::Dedent)
                        {
                            self.advance();
                        }
                        if self.check(&TokenKind::Comma) {
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    // Represent as StructInit with no type name (anonymous struct / named tuple)
                    Ok(Expr::StructInit {
                        name: "__tuple".to_string(),
                        fields,
                    })
                } else {

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

                } // end else (not named tuple)
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

                // Check for prefix list comprehension: [for x in items: expr]
                // or [for x in items if cond: expr]
                if self.check(&TokenKind::For) {
                    self.advance(); // consume 'for'
                    let (pattern, iterable, condition) = self.parse_comprehension_clause()?;
                    // Expect colon separator before the mapping expression
                    self.expect(&TokenKind::Colon)?;
                    let expr = self.parse_expression()?;
                    // Skip whitespace before closing bracket
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                    {
                        self.advance();
                    }
                    self.expect(&TokenKind::RBracket)?;
                    return Ok(Expr::ListComprehension {
                        expr: Box::new(expr),
                        pattern,
                        iterable: Box::new(iterable),
                        condition,
                    });
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

                // Check for repeat expression: [value; count]
                if self.check(&TokenKind::Semicolon) {
                    self.advance(); // consume ';'
                    let count = self.parse_expression()?;
                    // Skip whitespace before closing bracket
                    while self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                    {
                        self.advance();
                    }
                    self.expect(&TokenKind::RBracket)?;
                    // Represent as a Call to array repeat
                    return Ok(Expr::Call {
                        callee: Box::new(Expr::Identifier("__array_repeat".to_string())),
                        args: vec![
                            Argument { name: None, value: first },
                            Argument { name: None, value: count },
                        ],
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
                // Skip whitespace after opening brace (for multi-line dicts)
                self.skip_whitespace_tokens();
                // Empty dict
                if self.check(&TokenKind::RBrace) {
                    self.advance();
                    return Ok(Expr::Dict(Vec::new()));
                }

                // Check for block expression: { var x = 0; ... ; x }
                // If the first token is a statement keyword, treat as block expression
                if matches!(
                    &self.current.kind,
                    TokenKind::Var | TokenKind::Let | TokenKind::Const
                    | TokenKind::If | TokenKind::While | TokenKind::Loop
                    | TokenKind::Match | TokenKind::Return | TokenKind::Fn
                ) {
                    // Parse statements until closing brace
                    let mut stmts = Vec::new();
                    while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                        self.skip_whitespace_tokens();
                        if self.check(&TokenKind::RBrace) {
                            break;
                        }
                        stmts.push(self.parse_item()?);
                        self.skip_whitespace_tokens();
                        // Skip optional semicolons
                        while self.check(&TokenKind::Semicolon) {
                            self.advance();
                            self.skip_whitespace_tokens();
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    // Return the last expression as the block result, or nil
                    if let Some(Node::Expression(expr)) = stmts.last() {
                        return Ok(expr.clone());
                    }
                    return Ok(Expr::Nil);
                }

                // Check for dict spread: {**d1, **d2}
                if self.check(&TokenKind::DoubleStar) {
                    return self.parse_dict_with_spreads();
                }

                // Check for prefix-form dict/set comprehension: {for pattern in iterable: expr}
                if self.check(&TokenKind::For) {
                    self.advance();
                    let (pattern, iterable, condition) = self.parse_comprehension_clause()?;
                    // After the comprehension clause, expect colon and expression
                    self.expect(&TokenKind::Colon)?;
                    let body = self.parse_expression()?;
                    self.expect(&TokenKind::RBrace)?;
                    // Check if body is a tuple (key, value) for dict comprehension
                    // Otherwise treat as set comprehension
                    match &body {
                        Expr::Tuple(elems) if elems.len() == 2 => {
                            return Ok(Expr::DictComprehension {
                                key: Box::new(elems[0].clone()),
                                value: Box::new(elems[1].clone()),
                                pattern,
                                iterable: Box::new(iterable),
                                condition,
                            });
                        }
                        _ => {
                            // Set comprehension or general generator
                            return Ok(Expr::ListComprehension {
                                expr: Box::new(body),
                                pattern,
                                iterable: Box::new(iterable),
                                condition,
                            });
                        }
                    }
                }

                // Parse first key
                let key = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let value = self.parse_expression()?;

                // Skip whitespace after value
                self.skip_whitespace_tokens();

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
                    // Skip whitespace after comma
                    self.skip_whitespace_tokens();
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
                    // Skip whitespace after pair
                    self.skip_whitespace_tokens();
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
                // Disambiguate: new expression vs 'new' as identifier (variable/parameter name)
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if matches!(next.kind, TokenKind::RParen | TokenKind::Comma | TokenKind::RBracket
                    | TokenKind::RBrace | TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
                    | TokenKind::Assign | TokenKind::Colon | TokenKind::Semicolon
                    | TokenKind::PlusAssign | TokenKind::MinusAssign) {
                    self.advance();
                    return Ok(Expr::Identifier("new".to_string()));
                }
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
                // Disambiguate: match expression vs match as identifier (variable)
                // In expression context, 'match' is an identifier unless followed by
                // a token that looks like the start of a match subject expression
                // followed eventually by a colon (match SUBJECT:).
                // Safe heuristic: if next token is NOT an identifier, integer, string,
                // LParen, or similar expression-start, treat as identifier.
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // These tokens indicate 'match' is being used as a variable name
                let is_variable = matches!(next.kind,
                    TokenKind::Assign | TokenKind::Dot | TokenKind::LBracket
                    | TokenKind::PlusAssign | TokenKind::MinusAssign | TokenKind::StarAssign
                    | TokenKind::SlashAssign | TokenKind::PercentAssign
                    | TokenKind::Comma | TokenKind::RParen
                    | TokenKind::RBracket | TokenKind::RBrace | TokenKind::Newline
                    | TokenKind::Semicolon | TokenKind::Eof | TokenKind::Dedent
                    | TokenKind::Colon
                    // Binary/comparison operators
                    | TokenKind::Eq | TokenKind::NotEq | TokenKind::Lt | TokenKind::Gt
                    | TokenKind::LtEq | TokenKind::GtEq
                    | TokenKind::Plus | TokenKind::Minus | TokenKind::Star | TokenKind::Slash
                    | TokenKind::Percent | TokenKind::And | TokenKind::Or
                    | TokenKind::Pipe | TokenKind::Ampersand | TokenKind::Caret
                    | TokenKind::DoubleQuestion | TokenKind::Question
                );
                if is_variable {
                    self.advance();
                    return Ok(Expr::Identifier("match".to_string()));
                }
                self.advance();
                let subject = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                if self.check(&TokenKind::Newline) {
                    self.advance();
                    if self.check(&TokenKind::Indent) {
                        self.expect(&TokenKind::Indent)?;
                        let mut arms = Vec::new();
                        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            if self.check(&TokenKind::Dedent) {
                                break;
                            }
                            // Break if current token can't start a match arm pattern
                            // (e.g., `:` from an outer `if` condition: `if match x: ... _: false:`)
                            if self.check(&TokenKind::Colon)
                                || self.check(&TokenKind::FatArrow)
                                || self.check(&TokenKind::Arrow)
                                || self.check(&TokenKind::Assign)
                            {
                                // Pop the indent stack entry that was pushed by the Indent
                                // we consumed at the start. This prevents stale indent levels
                                // from generating spurious Dedent tokens later.
                                self.lexer.indent_stack.pop();
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
                    } else if self.check(&TokenKind::Case)
                        || matches!(&self.current.kind, TokenKind::Identifier(_))
                        || self.check(&TokenKind::Underscore)
                    {
                        let mut arms = Vec::new();
                        loop {
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            if self.is_at_end()
                                || self.check(&TokenKind::RParen)
                                || self.check(&TokenKind::RBrace)
                                || self.check(&TokenKind::Dedent)
                                || self.check(&TokenKind::Colon)
                            {
                                break;
                            }
                            arms.push(self.parse_match_arm_expr()?);
                            if self.check(&TokenKind::Semicolon) {
                                self.advance();
                            }
                        }
                        Ok(Expr::Match {
                            subject: Box::new(subject),
                            arms,
                        })
                    } else {
                        Ok(Expr::Match {
                            subject: Box::new(subject),
                            arms: vec![],
                        })
                    }
                } else {
                    let mut arms = Vec::new();
                    loop {
                        arms.push(self.parse_match_arm_expr()?);
                        if self.check(&TokenKind::Semicolon) {
                            self.advance();
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            if self.is_at_end()
                                || self.check(&TokenKind::Newline)
                                || self.check(&TokenKind::Dedent)
                                || self.check(&TokenKind::RParen)
                            {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    Ok(Expr::Match {
                        subject: Box::new(subject),
                        arms,
                    })
                }
            }
            TokenKind::Dollar => {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(Expr::Identifier(format!("${}", name)))
            }
            // Allow vec! macro invocation even though vec is now a keyword
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
                } else {
                    // Otherwise return as an identifier (for backward compatibility)
                    Ok(Expr::Identifier("vec".to_string()))
                }
            }
            // Simple keywords that can also be used as identifiers in expressions
            TokenKind::From => { self.advance(); Ok(Expr::Identifier("from".to_string())) }
            TokenKind::As => {
                self.advance();
                // Check if followed by a type name: `as Type` as standalone cast expression
                // This handles patterns like `func(value, as i64)` in desugared code
                if matches!(&self.current.kind,
                    TokenKind::Identifier(_) | TokenKind::Self_ | TokenKind::LParen
                    | TokenKind::LBracket | TokenKind::Fn | TokenKind::Ampersand | TokenKind::Star
                ) {
                    let target_type = self.parse_type()?;
                    Ok(Expr::TypeCast {
                        expr: Box::new(Expr::Identifier("_".to_string())),
                        target_type,
                    })
                } else {
                    Ok(Expr::Identifier("as".to_string()))
                }
            }
            TokenKind::In => { self.advance(); Ok(Expr::Identifier("in".to_string())) }
            TokenKind::Gpu => { self.advance(); Ok(Expr::Identifier("gpu".to_string())) }
            TokenKind::Me => { self.advance(); Ok(Expr::Identifier("me".to_string())) }
            TokenKind::Var => { self.advance(); Ok(Expr::Identifier("var".to_string())) }
            TokenKind::Alias => { self.advance(); Ok(Expr::Identifier("alias".to_string())) }
            TokenKind::Bitfield => { self.advance(); Ok(Expr::Identifier("bitfield".to_string())) }
            TokenKind::Dyn => { self.advance(); Ok(Expr::Identifier("dyn".to_string())) }
            TokenKind::Shared => { self.advance(); Ok(Expr::Identifier("shared".to_string())) }
            TokenKind::Context => { self.advance(); Ok(Expr::Identifier("context".to_string())) }
            TokenKind::To => { self.advance(); Ok(Expr::Identifier("to".to_string())) }
            TokenKind::NotTo => { self.advance(); Ok(Expr::Identifier("not_to".to_string())) }
            TokenKind::Const => { self.advance(); Ok(Expr::Identifier("const".to_string())) }
            TokenKind::Static => { self.advance(); Ok(Expr::Identifier("static".to_string())) }
            TokenKind::Extern => { self.advance(); Ok(Expr::Identifier("extern".to_string())) }
            TokenKind::Pub => { self.advance(); Ok(Expr::Identifier("pub".to_string())) }
            TokenKind::Priv => { self.advance(); Ok(Expr::Identifier("priv".to_string())) }
            TokenKind::Trait => { self.advance(); Ok(Expr::Identifier("trait".to_string())) }
            TokenKind::Mixin => { self.advance(); Ok(Expr::Identifier("mixin".to_string())) }
            TokenKind::Impl => { self.advance(); Ok(Expr::Identifier("impl".to_string())) }
            TokenKind::Union => { self.advance(); Ok(Expr::Identifier("union".to_string())) }
            TokenKind::Actor => { self.advance(); Ok(Expr::Identifier("actor".to_string())) }
            TokenKind::Macro => { self.advance(); Ok(Expr::Identifier("macro".to_string())) }
            TokenKind::With => { self.advance(); Ok(Expr::Identifier("with".to_string())) }
            TokenKind::Mod => { self.advance(); Ok(Expr::Identifier("mod".to_string())) }
            TokenKind::Unit => { self.advance(); Ok(Expr::Identifier("unit".to_string())) }
            TokenKind::Async => { self.advance(); Ok(Expr::Identifier("async".to_string())) }
            TokenKind::Await => { self.advance(); Ok(Expr::Identifier("await".to_string())) }
            TokenKind::Yield => { self.advance(); Ok(Expr::Identifier("yield".to_string())) }
            TokenKind::Super => { self.advance(); Ok(Expr::Identifier("super".to_string())) }
            TokenKind::Common => { self.advance(); Ok(Expr::Identifier("common".to_string())) }
            TokenKind::Requires => { self.advance(); Ok(Expr::Identifier("requires".to_string())) }
            TokenKind::Ensures => { self.advance(); Ok(Expr::Identifier("ensures".to_string())) }
            TokenKind::Invariant => { self.advance(); Ok(Expr::Identifier("invariant".to_string())) }
            TokenKind::Use => { self.advance(); Ok(Expr::Identifier("use".to_string())) }
            TokenKind::Import => { self.advance(); Ok(Expr::Identifier("import".to_string())) }
            TokenKind::Export => { self.advance(); Ok(Expr::Identifier("export".to_string())) }
            TokenKind::Case => { self.advance(); Ok(Expr::Identifier("case".to_string())) }
            TokenKind::Auto => { self.advance(); Ok(Expr::Identifier("auto".to_string())) }
            TokenKind::Mut => { self.advance(); Ok(Expr::Identifier("mut".to_string())) }
            TokenKind::Fn => {
                self.advance();
                // Check if this is an anonymous function: fn(params): body
                // or fn(): body or fn(args) (function call)
                if self.check(&TokenKind::LParen) {
                    // Parse arguments as expressions (works for both lambda params and call args)
                    let args = self.parse_arguments()?;
                    // If followed by '->' or ':', this is a lambda/anonymous function
                    if self.check(&TokenKind::Arrow) {
                        // fn(params) -> ReturnType: body
                        self.advance(); // consume '->'
                        let _ret_type = self.parse_type()?;
                        self.expect(&TokenKind::Colon)?;
                        let body = self.parse_fn_lambda_body()?;
                        // Convert args to lambda params
                        let params = args.into_iter().map(|a| {
                            let name = match a.value {
                                Expr::Identifier(n) => n,
                                _ => "_".to_string(),
                            };
                            LambdaParam { name, ty: None }
                        }).collect();
                        Ok(Expr::Lambda {
                            params,
                            body: Box::new(body),
                            move_mode: MoveMode::Copy,
                        })
                    } else if self.check(&TokenKind::Colon) {
                        self.advance(); // consume ':'
                        // Check if body is an indented block or inline expression
                        let body = self.parse_fn_lambda_body()?;
                        // Convert args to lambda params
                        let params = args.into_iter().map(|a| {
                            let name = match a.value {
                                Expr::Identifier(n) => n,
                                _ => "_".to_string(),
                            };
                            LambdaParam { name, ty: None }
                        }).collect();
                        Ok(Expr::Lambda {
                            params,
                            body: Box::new(body),
                            move_mode: MoveMode::Copy,
                        })
                    } else {
                        // Not a lambda, just fn(args) — treat as a call to fn
                        Ok(Expr::Call {
                            callee: Box::new(Expr::Identifier("fn".to_string())),
                            args,
                        })
                    }
                } else {
                    Ok(Expr::Identifier("fn".to_string()))
                }
            }
            TokenKind::Let => { self.advance(); Ok(Expr::Identifier("let".to_string())) }
            TokenKind::Struct => { self.advance(); Ok(Expr::Identifier("struct".to_string())) }
            TokenKind::Class => { self.advance(); Ok(Expr::Identifier("class".to_string())) }
            TokenKind::Enum => { self.advance(); Ok(Expr::Identifier("enum".to_string())) }
            TokenKind::True => { self.advance(); Ok(Expr::Bool(true)) }
            TokenKind::False => { self.advance(); Ok(Expr::Bool(false)) }
            TokenKind::PassDoNothing | TokenKind::PassDn | TokenKind::Pass => {
                self.advance();
                Ok(Expr::Nil) // No-op evaluates to nil
            }
            TokenKind::PassTodo => {
                self.advance();
                Ok(Expr::Nil) // TODO marker evaluates to nil
            }
            TokenKind::Underscore => {
                // Wildcard/discard in expression context
                self.advance();
                Ok(Expr::Identifier("_".to_string()))
            }
            TokenKind::Loop => {
                self.advance();
                Ok(Expr::Identifier("loop".to_string()))
            }
            TokenKind::DocComment(content) => {
                // Triple-quoted strings and doc comments used as expressions
                let value = content.clone();
                self.advance();
                Ok(Expr::String(value))
            }
            // `return` as expression (e.g., in match arms: `nil: return nil`)
            TokenKind::Return => {
                self.advance();
                let value = if !self.check(&TokenKind::Newline)
                    && !self.check(&TokenKind::Dedent)
                    && !self.check(&TokenKind::Eof)
                    && !self.check(&TokenKind::RParen)
                    && !self.check(&TokenKind::RBracket)
                    && !self.check(&TokenKind::RBrace)
                    && !self.check(&TokenKind::Semicolon)
                    && !self.is_at_end()
                {
                    Some(Box::new(self.parse_expression()?))
                } else {
                    None
                };
                // Wrap in a DoBlock containing a Return statement so the AST is valid
                Ok(Expr::DoBlock(vec![Node::Return(crate::ast::ReturnStmt {
                    span: self.previous.span,
                    value: value.map(|v| *v),
                })]))
            }
            // `break` as expression (e.g., in match arms)
            TokenKind::Break => {
                self.advance();
                let value = if !self.check(&TokenKind::Newline)
                    && !self.check(&TokenKind::Dedent)
                    && !self.check(&TokenKind::Eof)
                    && !self.is_at_end()
                {
                    // Check for a label
                    if let TokenKind::Identifier(_) = &self.current.kind {
                        Some(Box::new(self.parse_expression()?))
                    } else {
                        None
                    }
                } else {
                    None
                };
                Ok(Expr::DoBlock(vec![Node::Break(crate::ast::BreakStmt {
                    span: self.previous.span,
                    value: value.map(|v| *v),
                })]))
            }
            // `continue` as expression (e.g., in match arms)
            TokenKind::Continue => {
                self.advance();
                Ok(Expr::DoBlock(vec![Node::Continue(crate::ast::ContinueStmt {
                    span: self.previous.span,
                })]))
            }
            // `..expr` struct spread/update syntax
            TokenKind::DoubleDot => {
                self.advance();
                let expr = self.parse_expression()?;
                Ok(Expr::Spread(Box::new(expr)))
            }
            // `@name` as expression — intrinsic/decorator in expression context
            TokenKind::At => {
                self.advance(); // consume @
                if let TokenKind::Identifier(name) = &self.current.kind.clone() {
                    let name = format!("@{}", name);
                    self.advance();
                    // If followed by '(', parse as a call
                    if self.check(&TokenKind::LParen) {
                        let args = self.parse_arguments()?;
                        Ok(Expr::Call {
                            callee: Box::new(Expr::Identifier(name)),
                            args,
                        })
                    } else {
                        Ok(Expr::Identifier(name))
                    }
                } else {
                    Ok(Expr::Identifier("@".to_string()))
                }
            }
            // `...` (Ellipsis) as expression — used as spread or placeholder
            TokenKind::Ellipsis => {
                self.advance();
                Ok(Expr::Identifier("...".to_string()))
            }
            // `for` in expression context — could be a prefix-form list comprehension
            // [for x in items: expr] or [for (k, v) in dict: expr]
            TokenKind::For => {
                // This handles standalone `for` in expression position
                // The bracket-enclosed case [for ...] is handled in the LBracket arm
                self.advance();
                Ok(Expr::Identifier("for".to_string()))
            }
            // `while` in expression position
            TokenKind::While => {
                self.advance();
                Ok(Expr::Identifier("while".to_string()))
            }
            // `else` in expression context (continuation of if-else)
            TokenKind::Else => {
                self.advance();
                Ok(Expr::Identifier("else".to_string()))
            }
            // `.method()` at start of line — continuation chaining
            // In Simple, method chains can span multiple lines
            TokenKind::Dot => {
                // Treat `.method(args)` as a method call on an implicit receiver
                self.advance();
                let method = self.expect_method_name()?;
                if self.check(&TokenKind::LParen) {
                    let args = self.parse_arguments()?;
                    // Return as method call on a placeholder identifier
                    Ok(Expr::MethodCall {
                        receiver: Box::new(Expr::Identifier("_chain_".to_string())),
                        method,
                        args,
                    })
                } else {
                    // Field access on implicit receiver
                    Ok(Expr::FieldAccess {
                        receiver: Box::new(Expr::Identifier("_chain_".to_string())),
                        field: method,
                    })
                }
            }
            // DoubleSlash (//) as integer division operator or comment — treat as identifier
            TokenKind::DoubleSlash => {
                // Skip to end of line (treat as comment)
                while !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.is_at_end() {
                    self.advance();
                }
                self.parse_primary()
            }
            // Newline/Indent/Dedent in expression context — skip them
            TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent => {
                self.advance();
                self.parse_primary()
            }
            // `or` and `and` used as function/variable names: or(a, b), and(x, y)
            TokenKind::Or | TokenKind::And => {
                let name = if matches!(&self.current.kind, TokenKind::Or) { "or" } else { "and" };
                self.advance();
                Ok(Expr::Identifier(name.to_string()))
            }
            // Colon followed by identifier: symbol literal :name
            // The lexer sometimes produces Colon + Identifier instead of Symbol
            // when the previous token was expression-like (e.g., after an identifier
            // in no-paren call context: `func :sym, arg`)
            // Colon followed by identifier/keyword: symbol literal :name
            // The lexer sometimes produces Colon + Identifier/Keyword instead of Symbol
            // when the previous token was expression-like (e.g., after an identifier
            // in no-paren call context: `func :sym, arg`)
            // Keywords like `val`, `fn`, etc. can also appear as symbol names.
            TokenKind::Colon => {
                let next = self.pending_token.clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                // Check if the next token is any "word-like" token that could be a symbol name
                let is_symbol_name = matches!(next.kind,
                    TokenKind::Identifier(_)
                    | TokenKind::Let | TokenKind::Var | TokenKind::Fn | TokenKind::Me
                    | TokenKind::If | TokenKind::Elif | TokenKind::Else
                    | TokenKind::For | TokenKind::While | TokenKind::Loop
                    | TokenKind::Break | TokenKind::Continue | TokenKind::Return
                    | TokenKind::Match | TokenKind::Case
                    | TokenKind::Struct | TokenKind::Class | TokenKind::Enum
                    | TokenKind::Union | TokenKind::Trait | TokenKind::Mixin | TokenKind::Impl
                    | TokenKind::Actor | TokenKind::Pub | TokenKind::Priv
                    | TokenKind::Import | TokenKind::From | TokenKind::As
                    | TokenKind::Mod | TokenKind::Use | TokenKind::Export
                    | TokenKind::Common | TokenKind::Auto | TokenKind::Crate
                    | TokenKind::In | TokenKind::Is | TokenKind::Not
                    | TokenKind::And | TokenKind::Or
                    | TokenKind::Spawn | TokenKind::New | TokenKind::Self_ | TokenKind::Super
                    | TokenKind::Async | TokenKind::Await | TokenKind::Yield
                    | TokenKind::Move | TokenKind::Const | TokenKind::Static
                    | TokenKind::Type | TokenKind::Unit | TokenKind::Extern
                    | TokenKind::Context | TokenKind::With | TokenKind::Macro
                    | TokenKind::Shared | TokenKind::Gpu | TokenKind::Dyn
                    | TokenKind::Out | TokenKind::OutErr | TokenKind::Where
                    | TokenKind::Requires | TokenKind::Ensures | TokenKind::Invariant
                    | TokenKind::Old | TokenKind::Result
                    | TokenKind::To | TokenKind::NotTo
                    | TokenKind::PassDoNothing | TokenKind::PassDn | TokenKind::PassTodo | TokenKind::Pass
                    | TokenKind::Bitfield | TokenKind::Alias | TokenKind::Mut
                );
                if is_symbol_name {
                    self.advance(); // consume ':'
                    // Get the symbol name from the next token's lexeme
                    let name = self.current.lexeme.clone();
                    self.advance(); // consume the name token
                    Ok(Expr::Symbol(name))
                } else {
                    Err(ParseError::unexpected_token(
                        "expression",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
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
        // Skip optional 'case' keyword before pattern
        if self.check(&TokenKind::Case) {
            self.advance();
        }
        // Set flag so pattern parser won't try typed pattern (name: Type)
        self.in_match_arm_pattern = true;
        let pattern = self.parse_pattern()?;
        self.in_match_arm_pattern = false;
        // Handle `as Type` after pattern in match arms: case 'A' as u8:
        if self.check(&TokenKind::As) {
            self.advance(); // consume 'as'
            let _ty = self.parse_type()?; // consume the type
        }
        // Handle comma-separated or-patterns: case Int(_), Float(_), Bool(_):
        // Commas act as an alternative separator for or-patterns in match arms
        let pattern = if self.check(&TokenKind::Comma)
            && !self.check(&TokenKind::FatArrow)
        {
            let mut patterns = match pattern {
                Pattern::Or(ps) => ps,
                other => vec![other],
            };
            while self.check(&TokenKind::Comma) {
                self.advance();
                self.skip_whitespace_tokens();
                // If we hit `:` or `=>` or `if`, stop — the comma wasn't a pattern separator
                if self.check(&TokenKind::Colon)
                    || self.check(&TokenKind::FatArrow)
                    || self.check(&TokenKind::If)
                {
                    break;
                }
                self.in_match_arm_pattern = true;
                patterns.push(self.parse_single_pattern()?);
                self.in_match_arm_pattern = false;
            }
            if patterns.len() == 1 {
                patterns.into_iter().next().unwrap()
            } else {
                Pattern::Or(patterns)
            }
        } else {
            pattern
        };
        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };
        let body = if self.check(&TokenKind::FatArrow) {
            self.advance();
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else if self.check(&TokenKind::Colon) {
            self.advance();
            if self.check(&TokenKind::Newline) {
                self.advance(); // consume newline before block
                // Try standard block parsing first (works when Indent/Dedent are emitted)
                if self.check(&TokenKind::Indent) {
                    self.parse_block_after_newline()?
                } else {
                    // Inside brackets: no Indent/Dedent, parse statements until we hit
                    // a match-arm-starting token (case, pattern identifiers at same indent)
                    // or a closing bracket.
                    let block_start = self.current.span;
                    let mut statements = Vec::new();
                    while !self.is_at_end()
                        && !self.check(&TokenKind::Case)
                        && !self.check(&TokenKind::RParen)
                        && !self.check(&TokenKind::RBrace)
                        && !self.check(&TokenKind::RBracket)
                        && !self.check(&TokenKind::Dedent)
                    {
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.is_at_end()
                            || self.check(&TokenKind::Case)
                            || self.check(&TokenKind::RParen)
                            || self.check(&TokenKind::RBrace)
                            || self.check(&TokenKind::RBracket)
                            || self.check(&TokenKind::Dedent)
                        {
                            break;
                        }
                        statements.push(self.parse_item()?);
                        if self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }
                    Block {
                        span: Span::new(
                            block_start.start,
                            self.previous.span.end,
                            block_start.line,
                            block_start.column,
                        ),
                        statements,
                    }
                }
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else if self.check(&TokenKind::Arrow) {
            // Arrow (->) as match arm delimiter (alternative syntax)
            self.advance();
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else {
            return Err(ParseError::unexpected_token(
                "'=>' or ':'",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };
        Ok(MatchArm {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            pattern,
            guard,
            body,
        })
    }
}
