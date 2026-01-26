use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

mod collections;
mod control;
mod i18n;
mod identifiers;
mod lambdas;
mod literals;
mod math;

impl<'a> Parser<'a> {
    pub(crate) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
            // Placeholder syntax: _ in expressions (for placeholder lambdas like nums.map(_ * 2))
            // The _ is parsed as an identifier and later transformed in argument parsing
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr::Identifier("_".to_string()))
            }
            TokenKind::Integer(_)
            | TokenKind::TypedInteger(_, _)
            | TokenKind::Float(_)
            | TokenKind::TypedFloat(_, _)
            | TokenKind::String(_)
            | TokenKind::RawString(_)
            | TokenKind::TypedString(_, _)
            | TokenKind::TypedRawString(_, _)
            | TokenKind::FString(_)
            | TokenKind::Bool(_)
            | TokenKind::Nil
            | TokenKind::Symbol(_)
            | TokenKind::CustomBlock { .. } => self.parse_primary_literal(),
            TokenKind::I18nString { .. } | TokenKind::I18nFString { .. } => self.parse_i18n_literal(),
            TokenKind::Result
            | TokenKind::Identifier { .. }
            | TokenKind::Self_
            | TokenKind::Out
            | TokenKind::OutErr
            | TokenKind::Type
            | TokenKind::Feature
            | TokenKind::Scenario
            | TokenKind::Outline
            | TokenKind::Examples
            | TokenKind::Given
            | TokenKind::When
            | TokenKind::Then
            | TokenKind::AndThen
            | TokenKind::Context
            | TokenKind::Common
            | TokenKind::Vec
            | TokenKind::Gpu
            | TokenKind::Slice
            | TokenKind::Flat
            | TokenKind::Alias
            | TokenKind::Bounds
            | TokenKind::Default
            | TokenKind::New
            | TokenKind::Old
            | TokenKind::From
            | TokenKind::To => self.parse_primary_identifier(),
            TokenKind::Backslash | TokenKind::Pipe | TokenKind::Move => self.parse_primary_lambda(),
            // fn(): lambda syntax (alias for \:) - only in expression context
            // Check if fn is IMMEDIATELY followed by ( (no identifier) to distinguish from function definitions
            // fn(): ... => lambda
            // fn name(): ... => function definition (not allowed in expression position)
            TokenKind::Fn => {
                // Peek at next token to see if it's immediately LParen
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });

                // Only treat as lambda if IMMEDIATELY followed by (
                // This distinguishes fn(): from fn name():
                if matches!(next.kind, TokenKind::LParen) {
                    // Check that current and next tokens are adjacent (no whitespace/identifier between)
                    // In Simple, fn( is lambda, but fn foo( is function definition
                    self.parse_primary_lambda()
                } else {
                    return Err(ParseError::unexpected_token(
                        "expression",
                        "fn (function definitions are not expressions - use fn(): for lambdas)",
                        self.current.span,
                    ));
                }
            }
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => self.parse_primary_collection(),
            // Handle 'new' specially: if followed by a type (identifier, &, *, etc.), it's allocation
            // Otherwise, it's used as a variable name identifier
            TokenKind::New => {
                // Peek at next token
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });

                // Check if next token indicates allocation context: new Type, new &Type, new *Type
                match next.kind {
                    TokenKind::Identifier { .. }
                    | TokenKind::Ampersand
                    | TokenKind::Star
                    | TokenKind::Plus
                    | TokenKind::Minus => {
                        // Allocation: new Type(...) or new &Type(...)
                        self.parse_primary_control()
                    }
                    _ => {
                        // Identifier: used as variable name like 'is_new or new'
                        self.parse_primary_identifier()
                    }
                }
            }
            // Handle 'old' specially: if followed by (, it's contract old(x)
            // Otherwise, it's used as a variable name identifier
            TokenKind::Old => {
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });

                if matches!(next.kind, TokenKind::LParen) {
                    // Contract: old(x)
                    self.parse_primary_control()
                } else {
                    // Identifier: used as variable name
                    self.parse_primary_identifier()
                }
            }
            TokenKind::Spawn
            | TokenKind::Go
            | TokenKind::If
            | TokenKind::Elif
            | TokenKind::Match
            | TokenKind::Dollar => self.parse_primary_control(),
            TokenKind::Grid | TokenKind::Tensor => self.parse_primary_math(),
            _ => Err(ParseError::unexpected_token(
                "expression",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
