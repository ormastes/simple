//! Expression parsing for SUI templates (precedence climbing parser)

use super::{BinOp, Expr, ParseError, SuiParser, UnaryOp};
use crate::lexer::SuiTokenKind;

impl<'a> SuiParser<'a> {
    pub(super) fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;

        while matches!(self.peek_kind(), SuiTokenKind::Or) {
            self.advance();
            let right = self.parse_and()?;
            left = Expr::Binary {
                op: BinOp::Or,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_equality()?;

        while matches!(self.peek_kind(), SuiTokenKind::And) {
            self.advance();
            let right = self.parse_equality()?;
            left = Expr::Binary {
                op: BinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;

        loop {
            let op = match self.peek_kind() {
                SuiTokenKind::Eq => BinOp::Eq,
                SuiTokenKind::NotEq => BinOp::NotEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_comparison()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_addition()?;

        loop {
            let op = match self.peek_kind() {
                SuiTokenKind::Lt => BinOp::Lt,
                SuiTokenKind::Gt => BinOp::Gt,
                SuiTokenKind::LtEq => BinOp::LtEq,
                SuiTokenKind::GtEq => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            let right = self.parse_addition()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_addition(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_multiplication()?;

        loop {
            let op = match self.peek_kind() {
                SuiTokenKind::Plus => BinOp::Add,
                SuiTokenKind::Minus => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let right = self.parse_multiplication()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_multiplication(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_unary()?;

        loop {
            let op = match self.peek_kind() {
                SuiTokenKind::Star => BinOp::Mul,
                SuiTokenKind::Slash => BinOp::Div,
                SuiTokenKind::Percent => BinOp::Mod,
                _ => break,
            };
            self.advance();
            let right = self.parse_unary()?;
            left = Expr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::Minus => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(operand),
                })
            }
            SuiTokenKind::Not => {
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Expr::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(operand),
                })
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            match self.peek_kind() {
                SuiTokenKind::Dot => {
                    self.advance();
                    let field = self.expect_identifier()?;

                    // Check for method call
                    if self.peek_kind() == SuiTokenKind::LParen {
                        self.advance();
                        let args = self.parse_arguments()?;
                        self.expect(SuiTokenKind::RParen)?;
                        expr = Expr::MethodCall {
                            receiver: Box::new(expr),
                            method: field,
                            args,
                        };
                    } else {
                        expr = Expr::FieldAccess {
                            receiver: Box::new(expr),
                            field,
                        };
                    }
                }
                SuiTokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expression()?;
                    self.expect(SuiTokenKind::RBracket)?;
                    expr = Expr::IndexAccess {
                        receiver: Box::new(expr),
                        index: Box::new(index),
                    };
                }
                SuiTokenKind::LParen => {
                    self.advance();
                    let args = self.parse_arguments()?;
                    self.expect(SuiTokenKind::RParen)?;
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        args,
                    };
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::Integer(n) => {
                self.advance();
                Ok(Expr::Integer(n))
            }
            SuiTokenKind::Float(n) => {
                self.advance();
                Ok(Expr::Float(n))
            }
            SuiTokenKind::String(s) => {
                self.advance();
                Ok(Expr::String(s))
            }
            SuiTokenKind::Bool(b) => {
                self.advance();
                Ok(Expr::Bool(b))
            }
            SuiTokenKind::Identifier(name) => {
                self.advance();
                Ok(Expr::Identifier(name))
            }
            SuiTokenKind::LParen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(SuiTokenKind::RParen)?;
                Ok(expr)
            }
            SuiTokenKind::LBracket => {
                self.advance();
                let items = self.parse_arguments()?;
                self.expect(SuiTokenKind::RBracket)?;
                Ok(Expr::Array(items))
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "expression".to_string(),
                found: format!("{}", self.peek_kind()),
                line: self.peek().span.line,
                column: self.peek().span.column,
            }),
        }
    }

    fn parse_arguments(&mut self) -> Result<Vec<Expr>, ParseError> {
        // private, only called internally
        let mut args = Vec::new();

        if !matches!(
            self.peek_kind(),
            SuiTokenKind::RParen | SuiTokenKind::RBracket
        ) {
            args.push(self.parse_expression()?);

            while self.peek_kind() == SuiTokenKind::Comma {
                self.advance();
                if matches!(
                    self.peek_kind(),
                    SuiTokenKind::RParen | SuiTokenKind::RBracket
                ) {
                    break; // Allow trailing comma
                }
                args.push(self.parse_expression()?);
            }
        }

        Ok(args)
    }
}
