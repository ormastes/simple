use crate::ast::{Block, Expr, MatchArm, Node, PointerKind};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_control(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Old => self.parse_contract_old(),
            TokenKind::Forall => self.parse_forall(),
            TokenKind::Exists => self.parse_exists(),
            TokenKind::If | TokenKind::Elif => {
                self.advance();
                self.parse_if_expr()
            }
            TokenKind::Match => self.parse_match_expr(),
            TokenKind::Spawn => self.parse_spawn_expr(),
            TokenKind::Go => self.parse_go_expr(),
            TokenKind::New => self.parse_new_expr(),
            TokenKind::Dollar => self.parse_dollar_identifier(),
            _ => Err(ParseError::unexpected_token(
                "control expression",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_contract_old(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        self.expect(&TokenKind::LParen)?;
        let expr = self.parse_expression()?;
        self.expect(&TokenKind::RParen)?;
        Ok(Expr::ContractOld(Box::new(expr)))
    }

    /// Parse universal quantifier: forall x in range: predicate (VER-030)
    fn parse_forall(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'forall'

        // Parse pattern (variable binding)
        let pattern = self.parse_pattern()?;

        // Expect 'in'
        self.expect(&TokenKind::In)?;

        // Parse range expression
        let range = Box::new(self.parse_expression()?);

        // Expect colon
        self.expect(&TokenKind::Colon)?;

        // Parse predicate
        let predicate = Box::new(self.parse_expression()?);

        Ok(Expr::Forall {
            pattern,
            range,
            predicate,
        })
    }

    /// Parse existential quantifier: exists x in range: predicate (VER-030)
    fn parse_exists(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'exists'

        // Parse pattern (variable binding)
        let pattern = self.parse_pattern()?;

        // Expect 'in'
        self.expect(&TokenKind::In)?;

        // Parse range expression
        let range = Box::new(self.parse_expression()?);

        // Expect colon
        self.expect(&TokenKind::Colon)?;

        // Parse predicate
        let predicate = Box::new(self.parse_expression()?);

        Ok(Expr::Exists {
            pattern,
            range,
            predicate,
        })
    }

    fn parse_match_expr(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        let subject = self.parse_expression()?;
        // Enable forced indentation BEFORE consuming colon, so the newline after colon is preserved
        // This handles match expressions inside lambdas/parens where newlines would be suppressed
        self.lexer.enable_forced_indentation();
        self.expect(&TokenKind::Colon)?;
        if self.check(&TokenKind::Newline) {
            self.advance();
            self.expect(&TokenKind::Indent)?;
            let mut arms = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    break;
                }
                arms.push(self.parse_match_arm_expr()?);
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
            // Disable forced indentation after match body
            self.lexer.disable_forced_indentation();
            Ok(Expr::Match {
                subject: Box::new(subject),
                arms,
            })
        } else {
            // Disable forced indentation before returning error
            self.lexer.disable_forced_indentation();
            Err(ParseError::unexpected_token(
                "newline after match",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn parse_spawn_expr(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        let expr = self.parse_expression()?;
        Ok(Expr::Spawn(Box::new(expr)))
    }

    fn parse_go_expr(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume 'go'

        // Parse arguments: go(x, y) or go() or go
        let args = if self.check(&TokenKind::LParen) {
            self.advance(); // consume '('

            if self.check(&TokenKind::RParen) {
                // Empty parens: go() \ *: - capture all form
                self.advance();
                Vec::new()
            } else {
                // Parse argument expressions: go(x, y) \a, b: or go(x, y) \ *:
                let mut args = Vec::new();
                loop {
                    args.push(self.parse_expression()?);
                    if self.check(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                args
            }
        } else if self.check(&TokenKind::Backslash) {
            // Shorthand: go \ *: means capture all
            Vec::new()
        } else {
            return Err(ParseError::unexpected_token(
                "( or \\ after go",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Parse backslash
        self.expect(&TokenKind::Backslash)?;

        // Parse parameters or * for capture-all
        let mut params = Vec::new();
        if self.check(&TokenKind::Star) {
            // \ *: means capture all immutables
            self.advance();
        } else if !self.check(&TokenKind::Colon) {
            // Parse parameter list: \a, b, c:
            loop {
                params.push(self.expect_identifier()?);
                if self.check(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        // else: empty \: also means capture all (no * needed)

        // Parse colon
        self.expect(&TokenKind::Colon)?;

        // Parse body expression
        let body = Box::new(self.parse_expression()?);

        Ok(Expr::Go { args, params, body })
    }

    fn parse_new_expr(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        // new &Type(...) or new *Type(...)
        let kind = match &self.current.kind {
            TokenKind::Ampersand => {
                self.advance();
                PointerKind::Unique
            }
            TokenKind::Star => {
                self.advance();
                PointerKind::Shared
            }
            TokenKind::Minus => {
                self.advance();
                PointerKind::Weak
            }
            TokenKind::Plus => {
                self.advance();
                PointerKind::Handle
            }
            _ => PointerKind::Shared, // default
        };
        let expr = self.parse_postfix()?;
        Ok(Expr::New {
            kind,
            expr: Box::new(expr),
        })
    }

    fn parse_dollar_identifier(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        let name = self.expect_identifier()?;
        Ok(Expr::Identifier(format!("${}", name)))
    }

    fn parse_match_arm_expr(&mut self) -> Result<MatchArm, ParseError> {
        use crate::token::Span;
        let start_span = self.current.span;

        // Support both syntaxes:
        // - `case pattern:` or `case pattern ->`  (traditional)
        // - `| pattern ->`  (Erlang-style, preferred)
        let is_pipe_syntax = self.check(&TokenKind::Pipe);
        if is_pipe_syntax {
            self.advance(); // consume `|`
        } else if self.check(&TokenKind::Case) {
            self.advance();
        }

        let pattern = self.parse_pattern()?;
        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // For `| pattern ->` syntax, only accept `->`
        // For `case pattern:` syntax, accept `->`, `=>`, or `:`
        let valid_separator = if is_pipe_syntax {
            self.check(&TokenKind::Arrow)
        } else {
            self.check(&TokenKind::Arrow) || self.check(&TokenKind::FatArrow) || self.check(&TokenKind::Colon)
        };

        if !valid_separator {
            let expected = if is_pipe_syntax { "->" } else { "-> or => or :" };
            return Err(ParseError::unexpected_token(
                expected,
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }
        self.advance();
        let body = if self.check(&TokenKind::Newline) {
            self.parse_block()?
        } else {
            let expr = self.parse_expression()?;
            Block {
                span: self.previous.span,
                statements: vec![Node::Expression(expr)],
            }
        };
        Ok(MatchArm {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            guard,
            body,
        })
    }
}
