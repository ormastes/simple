use super::ParseError;
use super::{ClientBlock, ServerBlock};
use crate::lexer::SuiTokenKind;

impl<'a> super::SuiParser<'a> {
    /// Parse server block `{- ... -}`
    pub(super) fn parse_server_block(&mut self) -> Result<ServerBlock, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ServerOpen)?;

        let mut statements = Vec::new();
        while self.peek_kind() != SuiTokenKind::ServerClose && !self.is_at_end() {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        self.expect(SuiTokenKind::ServerClose)?;

        Ok(ServerBlock {
            span: start.merge(&self.previous().span),
            statements,
        })
    }

    /// Parse client block `{+ ... +}`
    pub(super) fn parse_client_block(&mut self) -> Result<ClientBlock, ParseError> {
        let start = self.peek().span;
        self.expect(SuiTokenKind::ClientOpen)?;

        let mut statements = Vec::new();
        while self.peek_kind() != SuiTokenKind::ClientClose && !self.is_at_end() {
            let stmt = self.parse_statement()?;
            statements.push(stmt);
        }

        self.expect(SuiTokenKind::ClientClose)?;

        Ok(ClientBlock {
            span: start.merge(&self.previous().span),
            statements,
        })
    }
}
