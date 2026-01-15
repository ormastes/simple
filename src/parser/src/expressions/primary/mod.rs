use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

mod collections;
mod control;
mod identifiers;
mod lambdas;
mod literals;
mod math;

impl<'a> Parser<'a> {
    pub(crate) fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind.clone() {
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
            | TokenKind::Symbol(_) => self.parse_primary_literal(),
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
            | TokenKind::Gpu => self.parse_primary_identifier(),
            TokenKind::Backslash | TokenKind::Pipe | TokenKind::Move => self.parse_primary_lambda(),
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                self.parse_primary_collection()
            }
            TokenKind::Old
            | TokenKind::Spawn
            | TokenKind::New
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
