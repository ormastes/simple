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
            s.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_class_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_class()?;
        if let Node::Class(ref mut c) = node {
            c.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_enum_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_enum()?;
        if let Node::Enum(ref mut e) = node {
            e.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_union_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_union()?;
        if let Node::Enum(ref mut e) = node {
            e.doc_comment = doc_comment;
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
