use crate::ast::{Expr, FStringPart};
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
            TokenKind::CustomBlock { kind, payload } => {
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
