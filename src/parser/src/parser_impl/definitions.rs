//! Type definition parsing
//!
//! This module handles parsing of struct, class, enum, union, and trait definitions
//! with doc comments.

use crate::ast::*;
use crate::error::ParseError;

use super::core::Parser;

impl<'a> Parser<'a> {
    pub(super) fn parse_struct_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_struct()?;
        if let Node::Struct(ref mut s) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            s.doc_comment = doc_comment.or(s.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_class_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_class()?;
        if let Node::Class(ref mut c) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            c.doc_comment = doc_comment.or(c.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_enum_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_enum()?;
        if let Node::Enum(ref mut e) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            e.doc_comment = doc_comment.or(e.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_union_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_union()?;
        if let Node::Enum(ref mut e) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            e.doc_comment = doc_comment.or(e.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_trait_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_trait()?;
        if let Node::Trait(ref mut t) = node {
            t.doc_comment = doc_comment;
        }
        Ok(node)
    }
}
