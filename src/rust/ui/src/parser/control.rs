use super::ParseError;
use super::{ControlNode, ForNode, IfNode, LetNode, TemplateNode};
use crate::lexer::{Span, SuiTokenKind};

impl<'a> super::SuiParser<'a> {
    /// Parse control flow `{% if/for/let %}`
    pub(super) fn parse_control(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ControlOpen)?;

        let control = match self.peek_kind() {
            SuiTokenKind::If => self.parse_if_control(start)?,
            SuiTokenKind::For => self.parse_for_control(start)?,
            SuiTokenKind::Let => self.parse_let_control(start)?,
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "if, for, or let".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        Ok(TemplateNode::Control(control))
    }

    /// Parse if control `{% if condition: %}...{% elif: %}...{% else: %}...{% end %}`
    fn parse_if_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::If)?;
        let condition = self.parse_expression()?;
        self.expect(SuiTokenKind::Colon)?;
        self.expect(SuiTokenKind::ControlClose)?;

        let then_branch = self.parse_control_body()?;

        let mut elif_branches = Vec::new();
        let mut else_branch = None;

        // Parse elif/else branches
        loop {
            if self.peek_kind() != SuiTokenKind::ControlOpen {
                break;
            }

            // Peek ahead to see what kind of control it is
            let saved = self.current;
            self.advance(); // consume {%

            match self.peek_kind() {
                SuiTokenKind::Elif => {
                    self.advance();
                    let elif_condition = self.parse_expression()?;
                    self.expect(SuiTokenKind::Colon)?;
                    self.expect(SuiTokenKind::ControlClose)?;
                    let elif_body = self.parse_control_body()?;
                    elif_branches.push((elif_condition, elif_body));
                }
                SuiTokenKind::Else => {
                    self.advance();
                    self.expect(SuiTokenKind::Colon)?;
                    self.expect(SuiTokenKind::ControlClose)?;
                    else_branch = Some(self.parse_control_body()?);
                    break;
                }
                SuiTokenKind::End => {
                    self.current = saved; // restore position
                    break;
                }
                _ => {
                    self.current = saved;
                    break;
                }
            }
        }

        // Expect end
        self.expect(SuiTokenKind::ControlOpen)?;
        self.expect(SuiTokenKind::End)?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::If(IfNode {
            span: start.merge(&self.previous().span),
            condition,
            then_branch,
            elif_branches,
            else_branch,
        }))
    }

    /// Parse for control `{% for item in collection: %}...{% end %}`
    fn parse_for_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::For)?;
        let binding = self.expect_identifier()?;

        // Optional index binding
        let index_binding = if self.peek_kind() == SuiTokenKind::Comma {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
        };

        self.expect(SuiTokenKind::In)?;
        let iterable = self.parse_expression()?;

        // Optional key expression
        let key = if let SuiTokenKind::Identifier(k) = self.peek_kind() {
            if k == "key" {
                self.advance();
                self.expect(SuiTokenKind::Assign)?;
                Some(self.parse_expression()?)
            } else {
                None
            }
        } else {
            None
        };

        self.expect(SuiTokenKind::Colon)?;
        self.expect(SuiTokenKind::ControlClose)?;

        let body = self.parse_control_body()?;

        self.expect(SuiTokenKind::ControlOpen)?;
        self.expect(SuiTokenKind::End)?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::For(ForNode {
            span: start.merge(&self.previous().span),
            binding,
            index_binding,
            iterable,
            key,
            body,
        }))
    }

    /// Parse let control `{% let name = expr %}`
    fn parse_let_control(&mut self, start: Span) -> Result<ControlNode, ParseError> {
        self.expect(SuiTokenKind::Let)?;
        let name = self.expect_identifier()?;
        self.expect(SuiTokenKind::Assign)?;
        let value = self.parse_expression()?;
        self.expect(SuiTokenKind::ControlClose)?;

        Ok(ControlNode::Let(LetNode {
            span: start.merge(&self.previous().span),
            name,
            value,
        }))
    }

    /// Parse control body (content until {% end/elif/else %})
    fn parse_control_body(&mut self) -> Result<Vec<TemplateNode>, ParseError> {
        let mut nodes = Vec::new();

        loop {
            if self.is_at_end() {
                break;
            }

            // Check for control block
            if self.peek_kind() == SuiTokenKind::ControlOpen {
                // Peek to see if it's end/elif/else
                let saved = self.current;
                self.advance();
                match self.peek_kind() {
                    SuiTokenKind::End | SuiTokenKind::Elif | SuiTokenKind::Else => {
                        self.current = saved;
                        break;
                    }
                    _ => {
                        self.current = saved;
                    }
                }
            }

            if let Some(node) = self.parse_template_node()? {
                nodes.push(node);
            }
        }

        Ok(nodes)
    }
}
