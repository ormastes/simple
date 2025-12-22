//! Parser helper methods - utility functions for tokenization, expectations, and generic parsing

use super::*;

impl<'a> Parser<'a> {
    pub(crate) fn advance(&mut self) {
        self.previous = std::mem::replace(
            &mut self.current,
            self.pending_token
                .take()
                .unwrap_or_else(|| self.lexer.next_token()),
        );
    }

    pub(crate) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current.kind) == std::mem::discriminant(kind)
    }

    pub(crate) fn is_at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    /// Peek at the next token without consuming current
    pub(crate) fn peek_is(&mut self, kind: &TokenKind) -> bool {
        // Save current state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        // Advance to peek
        self.advance();
        let result = self.check(kind);

        // Restore state
        self.pending_token = Some(self.current.clone());
        self.current = saved_current;
        self.previous = saved_previous;

        result
    }

    /// Parse array with spread operators: [*a, 1, *b]
    pub(crate) fn parse_array_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut elements = Vec::new();

        while !self.check(&TokenKind::RBracket) {
            if self.check(&TokenKind::Star) {
                self.advance();
                elements.push(Expr::Spread(Box::new(self.parse_expression()?)));
            } else {
                elements.push(self.parse_expression()?);
            }
            if !self.check(&TokenKind::RBracket) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(Expr::Array(elements))
    }

    /// Parse dict with spread operators: {**d1, "key": value, **d2}
    pub(crate) fn parse_dict_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut pairs = Vec::new();

        while !self.check(&TokenKind::RBrace) {
            if self.check(&TokenKind::DoubleStar) {
                self.advance(); // **
                let spread_expr = self.parse_expression()?;
                pairs.push((Expr::DictSpread(Box::new(spread_expr)), Expr::Nil));
            } else {
                let key = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let value = self.parse_expression()?;
                pairs.push((key, value));
            }
            if !self.check(&TokenKind::RBrace) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Expr::Dict(pairs))
    }

    pub(crate) fn expect(&mut self, kind: &TokenKind) -> Result<(), ParseError> {
        if self.check(kind) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                format!("{:?}", kind),
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    pub(crate) fn expect_identifier(&mut self) -> Result<String, ParseError> {
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            Ok(name)
        } else {
            Err(ParseError::unexpected_token(
                "identifier",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    pub(crate) fn check_ident(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier(current) if current == name)
    }

    pub(crate) fn expect_ident_value(&mut self, name: &str) -> Result<(), ParseError> {
        if self.check_ident(name) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                name,
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Expect an identifier or a keyword that can be used as a path segment.
    /// This allows using reserved words like 'unit', 'test', etc. in module paths.
    pub(crate) fn expect_path_segment(&mut self) -> Result<String, ParseError> {
        // First try regular identifier
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }

        // Allow certain keywords as path segments
        let name = match &self.current.kind {
            TokenKind::Unit => "unit",
            TokenKind::Type => "type",
            TokenKind::As => "as",
            TokenKind::In => "in",
            TokenKind::Is => "is",
            TokenKind::Or => "or",
            TokenKind::And => "and",
            TokenKind::Not => "not",
            TokenKind::Mod => "mod",
            TokenKind::Use => "use",
            TokenKind::Match => "match",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::For => "for",
            TokenKind::While => "while",
            TokenKind::Loop => "loop",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::Return => "return",
            TokenKind::True => "true",
            TokenKind::False => "false",
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };
        self.advance();
        Ok(name.to_string())
    }

    /// Expect an identifier or a keyword that can be used as a method/field name.
    /// This allows using reserved words like 'new', 'type', etc. as method names.
    pub(crate) fn expect_method_name(&mut self) -> Result<String, ParseError> {
        // First try regular identifier
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            return Ok(name);
        }

        // Allow certain keywords as method names
        let name = match &self.current.kind {
            TokenKind::New => "new",
            TokenKind::Type => "type",
            TokenKind::Unit => "unit",
            TokenKind::Match => "match",
            TokenKind::Is => "is",
            TokenKind::As => "as",
            TokenKind::In => "in",
            TokenKind::Or => "or",
            TokenKind::And => "and",
            TokenKind::Not => "not",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::For => "for",
            TokenKind::While => "while",
            TokenKind::Loop => "loop",
            TokenKind::Return => "return",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::Result => "result",
            TokenKind::Out => "out",
            TokenKind::OutErr => "out_err",
            // Infix keywords can also be method names
            TokenKind::To => "to",
            TokenKind::NotTo => "not_to",
            // Allow 'with' as method name for SIMD v.with(idx, val)
            TokenKind::With => "with",
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };
        self.advance();
        Ok(name.to_string())
    }

    /// Check if a type should be treated as a borrow type
    /// Types ending with _borrow are borrow references
    pub(crate) fn is_borrow_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Simple(name) => name.ends_with("_borrow"),
            Type::Generic { name, .. } => name.ends_with("_borrow"),
            _ => false,
        }
    }

    /// Parse generic type parameters: <T, U, V> or [T, U, V]
    /// Both angle brackets and square brackets are supported for compatibility
    /// Returns empty Vec if no generic parameters are present
    pub(crate) fn parse_generic_params(&mut self) -> Result<Vec<String>, ParseError> {
        // Check for angle brackets <T> or square brackets [T]
        let use_brackets = if self.check(&TokenKind::Lt) {
            self.advance(); // consume '<'
            false
        } else if self.check(&TokenKind::LBracket) {
            self.advance(); // consume '['
            true
        } else {
            return Ok(Vec::new());
        };

        let mut params = Vec::new();
        let end_token = if use_brackets {
            TokenKind::RBracket
        } else {
            TokenKind::Gt
        };

        while !self.check(&end_token) {
            let name = self.expect_identifier()?;
            params.push(name);

            if !self.check(&end_token) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        if use_brackets {
            self.expect(&TokenKind::RBracket)?; // consume ']'
        } else {
            self.expect(&TokenKind::Gt)?; // consume '>'
        }

        Ok(params)
    }
}
