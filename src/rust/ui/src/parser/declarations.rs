use super::ParseError;
use super::StateDecl;
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse a state declaration `{$ let name: Type $}`
    pub(super) fn parse_declaration(&mut self) -> Result<StateDecl, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::DeclOpen)?;
        self.expect(SuiTokenKind::Let)?;

        let name = self.expect_identifier()?;

        let ty = if self.peek_kind() == SuiTokenKind::Colon {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let default = if self.peek_kind() == SuiTokenKind::Assign {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect(SuiTokenKind::DeclClose)?;

        Ok(StateDecl {
            span: start.merge(&self.previous().span),
            name,
            ty,
            default,
        })
    }
}
