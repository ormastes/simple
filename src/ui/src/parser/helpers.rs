use super::ParseError;
use crate::lexer::{SuiToken, SuiTokenKind};

impl<'a> super::SuiParser<'a> {
    // ========================================================================
    // Helper methods
    // ========================================================================

    pub(super) fn peek(&self) -> &SuiToken {
        &self.tokens[self.current.min(self.tokens.len() - 1)]
    }

    pub(super) fn peek_kind(&self) -> SuiTokenKind {
        self.peek().kind.clone()
    }

    pub(super) fn previous(&self) -> &SuiToken {
        &self.tokens[(self.current - 1).max(0)]
    }

    pub(super) fn advance(&mut self) -> &SuiToken {
        if !self.is_at_end() {
            self.current += 1;
        }
        self.previous()
    }

    pub(super) fn is_at_end(&self) -> bool {
        self.peek_kind() == SuiTokenKind::Eof
    }

    pub(super) fn expect(&mut self, expected: SuiTokenKind) -> Result<(), ParseError> {
        if std::mem::discriminant(&self.peek_kind()) == std::mem::discriminant(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: format!("{}", expected),
                found: format!("{}", self.peek_kind()),
                line: self.peek().span.line,
                column: self.peek().span.column,
            })
        }
    }

    pub(super) fn expect_identifier(&mut self) -> Result<String, ParseError> {
        match self.peek_kind() {
            SuiTokenKind::Identifier(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: format!("{}", self.peek_kind()),
                line: self.peek().span.line,
                column: self.peek().span.column,
            }),
        }
    }
}
