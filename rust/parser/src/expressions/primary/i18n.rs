//! i18n expression parsing
//!
//! Parses:
//! - Simple i18n strings: `Name_"text"` -> I18nString
//! - i18n strings with args: `Name_"text"{key: value}` -> I18nTemplate
//! - i18n fstrings with args: `Name_"Hello {user}!"{user: name}` -> I18nTemplate

use crate::ast::{Expr, FStringPart};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{FStringToken, TokenKind};

impl<'a> Parser<'a> {
    /// Parse an i18n literal: I18nString or I18nFString token
    /// Optionally followed by {key: expr, ...} arguments
    pub(super) fn parse_i18n_literal(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::I18nString { name, default_text } => {
                let name = name.clone();
                let default_text = default_text.clone();
                self.advance();

                // Check for trailing {args}
                if self.check(&TokenKind::LBrace) {
                    let args = self.parse_i18n_args()?;
                    Ok(Expr::I18nTemplate {
                        name,
                        parts: vec![FStringPart::Literal(default_text)],
                        args,
                    })
                } else {
                    Ok(Expr::I18nString { name, default_text })
                }
            }
            TokenKind::I18nFString { name, parts } => {
                let name = name.clone();
                let parts = parts.clone();
                self.advance();

                // Parse the fstring parts into FStringPart
                let parsed_parts = self.parse_fstring_parts_from_tokens(&parts)?;

                // i18n fstrings with interpolation MUST have trailing {args}
                if self.check(&TokenKind::LBrace) {
                    let args = self.parse_i18n_args()?;
                    Ok(Expr::I18nTemplate {
                        name,
                        parts: parsed_parts,
                        args,
                    })
                } else {
                    // No args provided - this is an error for fstrings with interpolation
                    // since the template variables need values
                    // But we can still create an I18nTemplate with empty args
                    // The semantic checker can validate this later
                    Ok(Expr::I18nTemplate {
                        name,
                        parts: parsed_parts,
                        args: Vec::new(),
                    })
                }
            }
            _ => Err(ParseError::unexpected_token(
                "i18n literal",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse i18n arguments: {key: expr, key2: expr2}
    fn parse_i18n_args(&mut self) -> Result<Vec<(String, Expr)>, ParseError> {
        self.expect(&TokenKind::LBrace)?;
        let mut args = Vec::new();

        while !self.check(&TokenKind::RBrace) {
            // Parse key
            let key = self.expect_identifier()?;

            // Expect colon
            self.expect(&TokenKind::Colon)?;

            // Parse value expression
            let value = self.parse_expression()?;

            args.push((key, value));

            // Check for comma or end
            if !self.check(&TokenKind::RBrace) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(args)
    }

    /// Parse FStringToken vec into FStringPart vec
    fn parse_fstring_parts_from_tokens(&mut self, parts: &[FStringToken]) -> Result<Vec<FStringPart>, ParseError> {
        let mut result_parts = Vec::new();
        for part in parts {
            match part {
                FStringToken::Literal(s) => {
                    result_parts.push(FStringPart::Literal(s.clone()));
                }
                FStringToken::Expr(expr_str) => {
                    // Parse the expression string using expression parser
                    // (does not treat leading whitespace as indentation)
                    let mut sub_parser = Parser::new_expression(expr_str);
                    match sub_parser.parse_expression() {
                        Ok(expr) => {
                            // Verify the entire expression was consumed
                            if sub_parser.is_at_end() || matches!(sub_parser.current.kind, TokenKind::Eof) {
                                result_parts.push(FStringPart::Expr(expr));
                            } else {
                                // Expression didn't consume all input, treat as literal
                                result_parts.push(FStringPart::Literal(format!("{{{}}}", expr_str)));
                            }
                        }
                        Err(_) => {
                            // If parsing fails, treat as literal
                            result_parts.push(FStringPart::Literal(format!("{{{}}}", expr_str)));
                        }
                    }
                }
            }
        }
        Ok(result_parts)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Expr;
    use crate::parser_impl::core::Parser;

    #[test]
    fn test_parse_i18n_string_simple() {
        let mut parser = Parser::new(r#"Login_failed_"Login failed""#);
        let result = parser.parse_expression().unwrap();
        match result {
            Expr::I18nString { name, default_text } => {
                assert_eq!(name, "Login_failed_");
                assert_eq!(default_text, "Login failed");
            }
            _ => panic!("Expected I18nString"),
        }
    }

    #[test]
    fn test_parse_i18n_string_with_args() {
        let mut parser = Parser::new(r#"Greeting_"Hello!"{locale: "en"}"#);
        let result = parser.parse_expression().unwrap();
        match result {
            Expr::I18nTemplate { name, parts, args } => {
                assert_eq!(name, "Greeting_");
                assert_eq!(parts.len(), 1);
                assert_eq!(args.len(), 1);
                assert_eq!(args[0].0, "locale");
            }
            _ => panic!("Expected I18nTemplate"),
        }
    }

    #[test]
    fn test_parse_i18n_fstring() {
        let mut parser = Parser::new(r#"Welcome_"Hello {user}!"{user: name}"#);
        let result = parser.parse_expression().unwrap();
        match result {
            Expr::I18nTemplate { name, parts, args } => {
                assert_eq!(name, "Welcome_");
                assert_eq!(parts.len(), 3); // "Hello ", {user}, "!"
                assert_eq!(args.len(), 1);
                assert_eq!(args[0].0, "user");
            }
            _ => panic!("Expected I18nTemplate"),
        }
    }
}
