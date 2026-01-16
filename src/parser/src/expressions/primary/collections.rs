use crate::ast::{Expr, MoveMode};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_collection(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::LParen => self.parse_grouped_or_tuple(),
            TokenKind::LBracket => self.parse_array_literal(),
            TokenKind::LBrace => self.parse_dict_literal(),
            _ => Err(ParseError::unexpected_token(
                "collection",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_grouped_or_tuple(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        // Skip whitespace tokens inside parens (for multi-line expressions)
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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

    fn parse_array_literal(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        // Skip whitespace tokens inside brackets (for multi-line arrays)
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(Expr::Array(elements))
    }

    fn parse_dict_literal(&mut self) -> Result<Expr, ParseError> {
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
}
