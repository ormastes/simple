use super::ParseError;
use super::TypeExpr;
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    // ========================================================================
    // Type parsing
    // ========================================================================

    pub(super) fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.expect_identifier()?;

        // Check for generic args
        if self.peek_kind() == SuiTokenKind::LBracket {
            self.advance();
            let mut args = vec![self.parse_type()?];
            while self.peek_kind() == SuiTokenKind::Comma {
                self.advance();
                args.push(self.parse_type()?);
            }
            self.expect(SuiTokenKind::RBracket)?;
            return Ok(TypeExpr::Generic { name, args });
        }

        Ok(TypeExpr::Named(name))
    }
}
