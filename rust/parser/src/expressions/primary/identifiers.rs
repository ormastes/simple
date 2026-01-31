use crate::ast::Expr;
use crate::error::ParseError;
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
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
            TokenKind::Identifier { name, .. } => self.parse_identifier_or_struct(name),
            TokenKind::Self_ => {
                self.advance();
                Ok(Expr::Identifier("self".to_string()))
            }
            TokenKind::Super => {
                self.advance();
                Ok(Expr::Identifier("super".to_string()))
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
            // Allow math keywords to be used as identifiers outside m{} blocks
            TokenKind::Slice => self.parse_keyword_identifier("Slice"),
            TokenKind::Flat => self.parse_keyword_identifier("Flat"),
            TokenKind::Vec => self.parse_vec_keyword(),
            TokenKind::Gpu => {
                self.advance();
                Ok(Expr::Identifier("gpu".to_string()))
            }
            // Allow 'alias' to be used as identifier (e.g., `with resource as alias: captured = alias`)
            // The 'alias' keyword is only used in type aliasing context: `alias NewType = OldType`
            TokenKind::Alias => self.parse_keyword_identifier("alias"),
            // Allow 'bounds' to be used as identifier (variable name)
            // The 'bounds' keyword is only used in type constraint contexts
            TokenKind::Bounds => self.parse_keyword_identifier("bounds"),
            TokenKind::Default => self.parse_keyword_identifier("default"),
            // Allow 'new' and 'old' to be used as identifiers (variable names)
            // These are keywords only in specific contexts: new Type(...) and old(x)
            TokenKind::New => self.parse_keyword_identifier("new"),
            TokenKind::Old => self.parse_keyword_identifier("old"),
            // Allow 'from' and 'to' to be used as identifiers (variable names)
            // These are keywords only in specific contexts: from keyword in imports, to in ranges
            TokenKind::From => self.parse_keyword_identifier("from"),
            TokenKind::To => self.parse_keyword_identifier("to"),
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
        // DEPRECATED: Use dot syntax instead (Name.Variant)
        if self.check(&TokenKind::DoubleColon) {
            // Emit deprecation warning for :: syntax
            let colon_span = self.current.span;
            let warning = ErrorHint {
                level: ErrorHintLevel::Warning,
                message: "Deprecated syntax for static method/variant access".to_string(),
                span: colon_span,
                suggestion: Some("Use dot syntax (.) instead of double colon (::)".to_string()),
                help: Some("Example: Type.new() instead of Type::new()".to_string()),
            };
            self.error_hints.push(warning);

            let mut segments = vec![name];
            while self.check(&TokenKind::DoubleColon) {
                self.advance(); // consume '::'
                                // Use expect_method_name to allow keywords like 'new', 'type', etc.
                let segment = self.expect_method_name()?;
                segments.push(segment);
            }
            Ok(Expr::Path(segments))
        // Check for struct initialization: Name { field: value, ... }
        // Allow both uppercase (Point { x: 1 }) and lowercase (text { data: ptr }) names
        // Disambiguate from dict literals by checking if `{ identifier :` pattern follows
        } else if self.check(&TokenKind::LBrace) && !self.no_brace_postfix && (name.chars().next().map_or(false, |c| c.is_uppercase()) || self.peek_is_struct_init()) {
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
