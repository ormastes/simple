use crate::ast::{extract_fstring_keys, Expr, FStringPart, TypeMeta};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{FStringToken, TokenKind};

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_literal(&mut self) -> Result<Expr, ParseError> {
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
                            // Parse the expression string using expression parser
                            // (does not treat leading whitespace as indentation)
                            let mut sub_parser = Parser::new_expression(&expr_str);
                            match sub_parser.parse_expression() {
                                Ok(expr) => {
                                    // Verify the entire expression was consumed
                                    // If there's leftover content, treat as literal
                                    if sub_parser.is_at_end() || matches!(sub_parser.current.kind, TokenKind::Eof) {
                                        result_parts.push(FStringPart::Expr(expr));
                                    } else {
                                        // Expression didn't consume all input, treat as literal
                                        result_parts.push(FStringPart::Literal(format!("{{{}}}", expr_str)));
                                    }
                                }
                                Err(_) => {
                                    // If parsing fails, treat the whole thing as a literal
                                    // This allows strings like "re{ ^\\d{4} }" to work
                                    result_parts.push(FStringPart::Literal(format!("{{{}}}", expr_str)));
                                }
                            }
                        }
                    }
                }
                // Extract const_keys from placeholders and create TypeMeta
                let const_keys = extract_fstring_keys(&result_parts);
                let type_meta = TypeMeta::with_const_keys(const_keys);
                Ok(Expr::FString {
                    parts: result_parts,
                    type_meta,
                })
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
            TokenKind::CustomBlock { kind, payload, .. } => {
                // Custom block expression: m{...}, sh{...}, sql{...}, re{...}, etc.
                let kind = kind.clone();
                let payload = payload.clone();
                self.advance();
                Ok(Expr::BlockExpr { kind, payload })
            }
            _ => Err(ParseError::unexpected_token(
                "literal",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
