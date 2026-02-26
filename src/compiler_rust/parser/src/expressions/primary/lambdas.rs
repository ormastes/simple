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
            TokenKind::Fn => {
                // Lambda: fn(): expr or fn(x, y): expr (alias for backslash syntax)
                // This provides more familiar syntax for those coming from other languages
                self.advance();
                self.expect(&TokenKind::LParen)?;
                // Parse parameters inside parentheses (can be empty for fn():)
                let params = if self.check(&TokenKind::RParen) {
                    vec![]
                } else {
                    let (params, _capture_all) = self.parse_lambda_params()?;
                    params
                };
                self.expect(&TokenKind::RParen)?;
                // Enable forced indentation BEFORE consuming colon, so the newline after colon is preserved
                // This handles lambda expressions inside function call arguments where newlines would be suppressed
                self.lexer.enable_forced_indentation();
                self.expect(&TokenKind::Colon)?;

                // Parse body - can be inline expression or indented block
                let body = if self.check(&TokenKind::Newline) {
                    self.advance(); // consume newline

                    if self.check(&TokenKind::Indent) {
                        // Block body
                        self.advance(); // consume Indent

                        let mut statements = Vec::new();
                        while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
                            // Skip newlines between statements
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }

                            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                                break;
                            }

                            // Stop at closing brackets when the lambda body is inside a function call.
                            if matches!(self.current.kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                                break;
                            }

                            let stmt = self.parse_item()?;
                            statements.push(stmt);

                            // Skip trailing newlines
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                        }

                        // Consume dedent if present
                        if self.check(&TokenKind::Dedent) {
                            self.advance();
                        }

                        // Disable forced indentation after lambda body
                        self.lexer.disable_forced_indentation();

                        Expr::DoBlock(statements)
                    } else {
                        // Disable forced indentation - not a block
                        self.lexer.disable_forced_indentation();

                        // Single expression after newline
                        self.parse_expression()?
                    }
                } else {
                    // Inline expression - disable forced indentation after parsing
                    let expr = self.parse_expression()?;
                    self.lexer.disable_forced_indentation();
                    expr
                };

                Ok(Expr::Lambda {
                    params,
                    body: Box::new(body),
                    move_mode: MoveMode::Copy,
                    capture_all: false,
                })
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
