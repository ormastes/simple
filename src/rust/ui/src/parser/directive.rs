use super::ParseError;
use super::{Expr, HydrateStrategy, TemplateKind, TemplateNode};
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse the template directive `{@ page/component/layout Name @}`
    pub(super) fn parse_template_directive(
        &mut self,
    ) -> Result<(TemplateKind, String, Option<String>, Vec<(String, Expr)>), ParseError> {
        // Skip any leading content until we find a directive
        while !self.is_at_end() && self.peek_kind() != SuiTokenKind::DirectiveOpen {
            self.advance();
        }

        if self.is_at_end() {
            let (kind, name) = self.default_template();
            return Ok((kind, name, None, Vec::new()));
        }

        self.expect(SuiTokenKind::DirectiveOpen)?;

        let kind = match self.peek_kind() {
            SuiTokenKind::Page => {
                self.advance();
                TemplateKind::Page
            }
            SuiTokenKind::Component => {
                self.advance();
                TemplateKind::Component
            }
            SuiTokenKind::Layout => {
                self.advance();
                TemplateKind::Layout
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "page, component, or layout".to_string(),
                    found: format!("{}", self.peek_kind()),
                    line: self.peek().span.line,
                    column: self.peek().span.column,
                });
            }
        };

        let name = self.expect_identifier()?;

        // Parse optional layout and props
        let mut layout = None;
        let mut layout_props = Vec::new();

        while self.peek_kind() != SuiTokenKind::DirectiveClose {
            if let SuiTokenKind::Identifier(key) = self.peek_kind() {
                self.advance();
                if key == "layout" {
                    self.expect(SuiTokenKind::Assign)?;
                    layout = Some(self.expect_identifier()?);
                } else {
                    // It's a prop
                    self.expect(SuiTokenKind::Assign)?;
                    let value = self.parse_expression()?;
                    layout_props.push((key, value));
                }
            } else {
                break;
            }
        }

        self.expect(SuiTokenKind::DirectiveClose)?;

        Ok((kind, name, layout, layout_props))
    }

    /// Parse directive node (embed, slot, fill)
    pub(super) fn parse_template_directive_node(&mut self) -> Result<TemplateNode, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::DirectiveOpen)?;

        match self.peek_kind() {
            SuiTokenKind::Embed => {
                self.advance();
                let component = self.expect_identifier()?;
                let mut props = Vec::new();
                let mut hydrate = HydrateStrategy::default();

                while self.peek_kind() != SuiTokenKind::DirectiveClose {
                    // Handle both identifiers and the 'hydrate' keyword
                    let key = match self.peek_kind() {
                        SuiTokenKind::Identifier(k) => {
                            self.advance();
                            k
                        }
                        SuiTokenKind::Hydrate => {
                            self.advance();
                            "hydrate".to_string()
                        }
                        _ => break,
                    };

                    self.expect(SuiTokenKind::Assign)?;

                    if key == "hydrate" {
                        if let SuiTokenKind::String(s) = self.peek_kind() {
                            self.advance();
                            hydrate = HydrateStrategy::from_str(&s).unwrap_or_default();
                        }
                    } else {
                        let value = self.parse_expression()?;
                        props.push((key, value));
                    }
                }

                self.expect(SuiTokenKind::DirectiveClose)?;

                Ok(TemplateNode::Embed(super::EmbedNode {
                    span: start.merge(&self.previous().span),
                    component,
                    props,
                    hydrate,
                }))
            }
            SuiTokenKind::Slot => {
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(SuiTokenKind::DirectiveClose)?;

                Ok(TemplateNode::Slot(super::SlotNode {
                    span: start.merge(&self.previous().span),
                    name,
                    default: None,
                }))
            }
            SuiTokenKind::Fill => {
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(SuiTokenKind::DirectiveClose)?;

                // Parse content until {@ end @}
                let mut content = Vec::new();
                loop {
                    if self.is_at_end() {
                        break;
                    }
                    if self.peek_kind() == SuiTokenKind::DirectiveOpen {
                        let saved = self.current;
                        self.advance();
                        if self.peek_kind() == SuiTokenKind::End {
                            self.advance();
                            self.expect(SuiTokenKind::DirectiveClose)?;
                            break;
                        }
                        self.current = saved;
                    }
                    if let Some(node) = self.parse_template_node()? {
                        content.push(node);
                    }
                }

                Ok(TemplateNode::Fill(super::FillNode {
                    span: start.merge(&self.previous().span),
                    name,
                    content,
                }))
            }
            _ => {
                // Skip unknown directives
                while self.peek_kind() != SuiTokenKind::DirectiveClose && !self.is_at_end() {
                    self.advance();
                }
                self.expect(SuiTokenKind::DirectiveClose)?;
                Ok(TemplateNode::Comment("Unknown directive".to_string()))
            }
        }
    }
}
