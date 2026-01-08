use super::ParseError;
use super::{Attribute, AttributeValue, Expr};
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse an HTML attribute
    pub(super) fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start = self.peek().span;
        let name = self.expect_identifier()?;

        // Check for special attribute prefixes
        if name.starts_with("on:") {
            // Event handler
            let event = name[3..].to_string();
            self.expect(SuiTokenKind::Assign)?;
            let handler = self.parse_attribute_value_expr()?;
            return Ok(Attribute {
                span: start.merge(&self.previous().span),
                name,
                value: AttributeValue::Event { event, handler },
            });
        }

        if name.starts_with("class:") {
            // Conditional class
            let class = name[6..].to_string();
            self.expect(SuiTokenKind::Assign)?;
            let condition = self.parse_attribute_value_expr()?;
            return Ok(Attribute {
                span: start.merge(&self.previous().span),
                name,
                value: AttributeValue::ConditionalClass { class, condition },
            });
        }

        // Check if there's a value
        if self.peek_kind() != SuiTokenKind::Assign {
            // Boolean attribute
            return Ok(Attribute {
                span: start,
                name,
                value: AttributeValue::Boolean,
            });
        }

        self.expect(SuiTokenKind::Assign)?;

        // Parse value
        let value = match self.peek_kind() {
            SuiTokenKind::String(s) => {
                self.advance();
                AttributeValue::Static(s)
            }
            SuiTokenKind::OutputOpen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(SuiTokenKind::OutputClose)?;
                AttributeValue::Dynamic(expr)
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "string or {{ expression }}".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        Ok(Attribute {
            span: start.merge(&self.previous().span),
            name,
            value,
        })
    }

    /// Parse an attribute value expression (handles both quoted and {{ }})
    pub(super) fn parse_attribute_value_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::String(s) => {
                self.advance();
                Ok(Expr::String(s))
            }
            SuiTokenKind::OutputOpen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(SuiTokenKind::OutputClose)?;
                Ok(expr)
            }
            _ => self.parse_expression(),
        }
    }
}
