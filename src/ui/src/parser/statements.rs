use super::ParseError;
use super::Statement;
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    pub(super) fn parse_statement(&mut self) -> Result<Statement, ParseError> {
        // Skip newlines
        while self.peek_kind() == SuiTokenKind::Newline {
            self.advance();
        }

        match self.peek_kind() {
            SuiTokenKind::Let => {
                self.advance();
                let name = self.expect_identifier()?;
                let ty = if self.peek_kind() == SuiTokenKind::Colon {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                self.expect(SuiTokenKind::Assign)?;
                let value = self.parse_expression()?;
                Ok(Statement::Let { name, ty, value })
            }
            SuiTokenKind::If => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let then_block = self.parse_statement_block()?;
                let else_block = if self.peek_kind() == SuiTokenKind::Else {
                    self.advance();
                    self.expect(SuiTokenKind::Colon)?;
                    Some(self.parse_statement_block()?)
                } else {
                    None
                };
                Ok(Statement::If {
                    condition,
                    then_block,
                    else_block,
                })
            }
            SuiTokenKind::For => {
                self.advance();
                let binding = self.expect_identifier()?;
                self.expect(SuiTokenKind::In)?;
                let iterable = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let body = self.parse_statement_block()?;
                Ok(Statement::For {
                    binding,
                    iterable,
                    body,
                })
            }
            SuiTokenKind::While => {
                self.advance();
                let condition = self.parse_expression()?;
                self.expect(SuiTokenKind::Colon)?;
                let body = self.parse_statement_block()?;
                Ok(Statement::While { condition, body })
            }
            SuiTokenKind::Break => {
                self.advance();
                Ok(Statement::Break)
            }
            SuiTokenKind::Continue => {
                self.advance();
                Ok(Statement::Continue)
            }
            SuiTokenKind::Identifier(name) => {
                self.advance();
                if self.peek_kind() == SuiTokenKind::Assign {
                    self.advance();
                    let value = self.parse_expression()?;
                    Ok(Statement::Assignment { target: name, value })
                } else {
                    // It's an expression starting with identifier
                    // Put it back and parse as expression
                    self.current -= 1;
                    let expr = self.parse_expression()?;
                    Ok(Statement::Expr(expr))
                }
            }
            _ => {
                let expr = self.parse_expression()?;
                Ok(Statement::Expr(expr))
            }
        }
    }

    pub(super) fn parse_statement_block(&mut self) -> Result<Vec<Statement>, ParseError> {
        // For now, parse single statement (multi-line blocks need indentation handling)
        let stmt = self.parse_statement()?;
        Ok(vec![stmt])
    }
}
