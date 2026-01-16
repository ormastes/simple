use crate::ast::{Block, Expr, MatchArm, Node, PointerKind};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_primary_control(&mut self) -> Result<Expr, ParseError> {
        match &self.current.kind {
            TokenKind::Old => self.parse_contract_old(),
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

    fn parse_match_expr(&mut self) -> Result<Expr, ParseError> {
        self.advance();
        let subject = self.parse_expression()?;
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
            Ok(Expr::Match {
                subject: Box::new(subject),
                arms,
            })
        } else {
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

        // Check for capture form |captures| or args form (args)
        let (args, is_capture_form) = if self.check(&TokenKind::Pipe) {
            // Capture form: go |x, y| \: expr
            self.advance(); // consume '|'
            let mut captures = Vec::new();
            while !self.check(&TokenKind::Pipe) && !self.is_at_end() {
                captures.push(Expr::Identifier(self.expect_identifier()?));
                if self.check(&TokenKind::Comma) {
                    self.advance();
                }
            }
            self.expect(&TokenKind::Pipe)?; // consume closing '|'
            (captures, true)
        } else if self.check(&TokenKind::LParen) {
            // Args form: go(x, y) \a, b: expr
            self.advance(); // consume '('
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) && !self.is_at_end() {
                args.push(self.parse_expression()?);
                if self.check(&TokenKind::Comma) {
                    self.advance();
                }
            }
            self.expect(&TokenKind::RParen)?; // consume ')'
            (args, false)
        } else {
            return Err(ParseError::unexpected_token(
                "( or | after go",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        // Parse backslash and parameters
        self.expect(&TokenKind::Backslash)?; // consume '\'
        let mut params = Vec::new();

        // For capture form, params are optional (can be just \:)
        // For args form, we need params
        if !self.check(&TokenKind::Colon) {
            // Parse parameters
            loop {
                params.push(self.expect_identifier()?);
                if self.check(&TokenKind::Comma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        // Parse colon
        self.expect(&TokenKind::Colon)?;

        // Parse body expression
        let body = Box::new(self.parse_expression()?);

        Ok(Expr::Go {
            args,
            params,
            is_capture_form,
            body,
        })
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
        let pattern = self.parse_pattern()?;
        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };
        // Accept both -> and => for match arms
        if !self.check(&TokenKind::Arrow) && !self.check(&TokenKind::FatArrow) {
            return Err(ParseError::unexpected_token(
                "-> or =>",
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
