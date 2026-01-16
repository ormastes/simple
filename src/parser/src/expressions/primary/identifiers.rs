use crate::ast::Expr;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_identifier(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Result => {
                // Allow 'result' as a regular identifier (like 'type', 'out', etc.)
                // ContractResult expression is only generated in contract blocks
                self.advance();
                Ok(Expr::Identifier("result".to_string()))
            }
            TokenKind::Identifier { name: name, .. } => self.parse_identifier_or_struct(name),
            TokenKind::Self_ => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
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
            TokenKind::Feature => self.parse_keyword_identifier("feature"),
            TokenKind::Scenario => self.parse_keyword_identifier("scenario"),
            TokenKind::Outline => self.parse_keyword_identifier("outline"),
            TokenKind::Examples => self.parse_keyword_identifier("examples"),
            TokenKind::Given => self.parse_keyword_identifier("given"),
            TokenKind::When => self.parse_keyword_identifier("when"),
            TokenKind::Then => self.parse_keyword_identifier("then"),
            TokenKind::AndThen => self.parse_keyword_identifier("and_then"),
            TokenKind::Context => self.parse_keyword_identifier("context"),
            TokenKind::Common => self.parse_keyword_identifier("common"),
            TokenKind::Vec => self.parse_vec_keyword(),
            TokenKind::Gpu => {
                self.advance();
                Ok(Expr::Identifier("gpu".to_string()))
            }
            _ => Err(ParseError::unexpected_token(
                "identifier",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_keyword_identifier(&mut self, keyword: &str) -> Result<Expr, ParseError> {
        self.advance();
        Ok(Expr::Identifier(keyword.to_string()))
    }

    fn parse_identifier_or_struct(&mut self, name: &str) -> Result<Expr, ParseError> {
        let name = name.to_string();
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
        } else if self.check(&TokenKind::LBrace) && name.chars().next().map_or(false, |c| c.is_uppercase()) {
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

    fn parse_vec_keyword(&mut self) -> Result<Expr, ParseError> {
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
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
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
}
