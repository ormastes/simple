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
                let parse_complete_expr = |source: &str| {
                    let mut parser = Parser::new_expression(source);
                    match parser.parse_expression() {
                        Ok(expr) if parser.is_at_end() || matches!(parser.current.kind, TokenKind::Eof) => Some(expr),
                        _ => None,
                    }
                };
                for part in parts {
                    match part {
                        FStringToken::Literal(s) => {
                            result_parts.push(FStringPart::Literal(s));
                        }
                        FStringToken::Expr(expr_str) => {
                            if let Some(expr) = parse_complete_expr(&expr_str) {
                                result_parts.push(FStringPart::Expr(expr));
                            } else {
                                // Keep brace-bearing regex/CSS text compatible.
                                result_parts.push(FStringPart::Literal(format!("{{{}}}", expr_str)));
                            }
                        }
                        FStringToken::ExprWithFormat(expr_str, format_spec) => {
                            if let Some(expr) = parse_complete_expr(&expr_str) {
                                result_parts.push(FStringPart::ExprWithFormat(expr, format_spec));
                            } else {
                                // A top-level colon can belong to the expression grammar
                                // (`if cond: yes else: no`). The lexer only marks a format
                                // candidate, so retry the complete hole before literalizing it.
                                let complete = format!("{}:{}", expr_str, format_spec);
                                if let Some(expr) = parse_complete_expr(&complete) {
                                    result_parts.push(FStringPart::Expr(expr));
                                } else {
                                    result_parts.push(FStringPart::Literal(format!("{{{}}}", complete)));
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
            TokenKind::Atom(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::Atom(s))
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
