use crate::ast::{Expr, MoveMode};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_lambda(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Backslash => {
                // Lambda: \x: expr or \x, y: expr or \: expr
                self.advance();
                self.parse_lambda_body(MoveMode::Copy)
            }
            TokenKind::Pipe => {
                // Lambda: |x| body or |x, y| body (Ruby/Rust style)
                self.advance();
                let params = self.parse_pipe_lambda_params()?;
                self.expect(&TokenKind::Pipe)?;
                let body = self.parse_expression()?;
                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                    move_mode: MoveMode::Copy,
                    capture_all: false, // Pipe syntax doesn't support capture-all
                })
            }
            TokenKind::Move => {
                // Move closure: move \x: expr
                self.advance();
                if !self.check(&TokenKind::Backslash) {
                    return Err(ParseError::unexpected_token(
                        "'\\'",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
                self.advance();
                self.parse_lambda_body(MoveMode::Move)
            }
            _ => Err(ParseError::unexpected_token(
                "lambda",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
