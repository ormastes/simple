//! Doc comment parsing
//!
//! This module handles parsing of doc comments (///) and attaching them to items.

use crate::ast::DocComment;
use crate::token::TokenKind;

use super::core::Parser;

impl<'a> Parser<'a> {
    /// Try to parse a doc comment if one is present.
    /// Returns None if no doc comment, Some(DocComment) if found.
    /// Merges consecutive doc comments into a single DocComment.
    pub(super) fn try_parse_doc_comment(&mut self) -> Option<DocComment> {
        // Skip newlines before doc comment
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        let mut contents = Vec::new();

        // Collect all consecutive doc comments
        while let TokenKind::DocComment(content) = &self.current.kind {
            let content = content.clone();
            contents.push(content);
            self.advance();
            // Skip newlines between doc comments
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if contents.is_empty() {
            None
        } else {
            // Merge all doc comments with newlines
            Some(DocComment::new(contents.join("\n")))
        }
    }
}
