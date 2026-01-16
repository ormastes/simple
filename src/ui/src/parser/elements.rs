use super::ParseError;
use super::{Element, TemplateNode};
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse an HTML element
    pub(super) fn parse_element(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::TagOpen)?;

        let tag = self.expect_identifier()?;
        let mut element = Element::new(tag.clone());
        element.span = start;

        // Parse attributes
        while !matches!(self.peek_kind(), SuiTokenKind::TagClose | SuiTokenKind::TagSelfClose) {
            if self.is_at_end() {
                return Err(ParseError::UnclosedBlock {
                    block_type: format!("<{}>", tag),
                    line: start.line,
                    column: start.column,
                });
            }
            let attr = self.parse_attribute()?;
            element.attrs.push(attr);
        }

        // Check for self-closing tag
        if self.peek_kind() == SuiTokenKind::TagSelfClose {
            self.advance();
            element.self_closing = true;
            return Ok(TemplateNode::Element(element));
        }

        self.expect(SuiTokenKind::TagClose)?;

        // Parse children until closing tag
        loop {
            if self.is_at_end() {
                return Err(ParseError::UnclosedBlock {
                    block_type: format!("<{}>", tag),
                    line: start.line,
                    column: start.column,
                });
            }

            // Check for closing tag
            if self.peek_kind() == SuiTokenKind::TagEndOpen {
                self.advance();
                let closing_tag = self.expect_identifier()?;
                if closing_tag != tag {
                    return Err(ParseError::InvalidTemplate {
                        message: format!("Mismatched closing tag: expected </{}>, found </{}>", tag, closing_tag),
                        line: self.previous().span.line,
                        column: self.previous().span.column,
                    });
                }
                self.expect(SuiTokenKind::TagClose)?;
                break;
            }

            if let Some(child) = self.parse_template_node()? {
                element.children.push(child);
            }
        }

        element.span = start.merge(&self.previous().span);
        Ok(TemplateNode::Element(element))
    }
}
