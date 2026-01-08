use super::ParseError;
use super::{SuiTemplate, TemplateKind};
use crate::lexer::{SuiLexer, SuiToken, SuiTokenKind};

/// SUI template parser
pub struct SuiParser<'a> {
    pub(super) tokens: Vec<SuiToken>,
    pub(super) current: usize,
    pub(super) source: &'a str,
}

impl<'a> SuiParser<'a> {
    /// Create a new parser for the given source
    pub fn new(source: &'a str) -> Self {
        let mut lexer = SuiLexer::new(source);
        let tokens = lexer.tokenize();
        Self {
            tokens,
            current: 0,
            source,
        }
    }

    /// Parse the template
    pub fn parse(&mut self) -> Result<SuiTemplate, ParseError> {
        // Look for directive to determine template kind
        let (kind, name, layout, layout_props) = self.parse_template_directive()?;

        let mut template = SuiTemplate::new(kind, name);
        template.layout = layout;
        template.layout_props = layout_props;

        // Parse declarations, server/client blocks, and content
        while !self.is_at_end() {
            match self.peek_kind() {
                SuiTokenKind::DeclOpen => {
                    let decl = self.parse_declaration()?;
                    template.declarations.push(decl);
                }
                SuiTokenKind::ServerOpen => {
                    let block = self.parse_server_block()?;
                    template.server_block = Some(block);
                }
                SuiTokenKind::ClientOpen => {
                    let block = self.parse_client_block()?;
                    template.client_block = Some(block);
                }
                _ => {
                    let node = self.parse_template_node()?;
                    if let Some(node) = node {
                        template.content.push(node);
                    }
                }
            }
        }

        Ok(template)
    }

    pub(super) fn default_template(&self) -> (TemplateKind, String) {
        (TemplateKind::Component, "Anonymous".to_string())
    }
}
