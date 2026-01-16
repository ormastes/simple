use super::ParseError;
use super::{TemplateNode, TextNode};
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse a template node (element, text, output, control, etc.)
    pub(super) fn parse_template_node(&mut self) -> Result<Option<TemplateNode>, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::TagOpen => Ok(Some(self.parse_element()?)),
            SuiTokenKind::TagEndOpen => {
                // Closing tag - return None to let parent handle it
                Ok(None)
            }
            SuiTokenKind::Text(text) => {
                let span = self.peek().span;
                self.advance();
                Ok(Some(TemplateNode::Text(TextNode { span, content: text })))
            }
            SuiTokenKind::OutputOpen => Ok(Some(self.parse_output(false)?)),
            SuiTokenKind::RawOutputOpen => Ok(Some(self.parse_output(true)?)),
            SuiTokenKind::ControlOpen => Ok(Some(self.parse_control()?)),
            SuiTokenKind::DirectiveOpen => Ok(Some(self.parse_template_directive_node()?)),
            SuiTokenKind::CommentOpen => {
                self.advance();
                if let SuiTokenKind::Comment(content) = self.peek_kind() {
                    self.advance();
                    Ok(Some(TemplateNode::Comment(content)))
                } else {
                    Ok(Some(TemplateNode::Comment(String::new())))
                }
            }
            SuiTokenKind::Eof => Ok(None),
            SuiTokenKind::Newline | SuiTokenKind::Whitespace => {
                self.advance();
                Ok(None)
            }
            _ => {
                // Skip unexpected tokens
                self.advance();
                Ok(None)
            }
        }
    }

    /// Parse output expression `{{ expr }}` or `{! expr !}`
    pub(super) fn parse_output(&mut self, raw: bool) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;

        if raw {
            self.expect(SuiTokenKind::RawOutputOpen)?;
        } else {
            self.expect(SuiTokenKind::OutputOpen)?;
        }

        let expr = self.parse_expression()?;

        if raw {
            self.expect(SuiTokenKind::RawOutputClose)?;
        } else {
            self.expect(SuiTokenKind::OutputClose)?;
        }

        let node = super::OutputNode {
            span: start.merge(&self.previous().span),
            expr,
        };

        if raw {
            Ok(TemplateNode::RawOutput(node))
        } else {
            Ok(TemplateNode::Output(node))
        }
    }
}
