//! Type definition parsing
//!
//! This module handles parsing of struct, class, enum, union, and trait definitions
//! with doc comments, as well as alias definitions.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

impl<'a> Parser<'a> {
    pub(super) fn parse_struct_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_struct()?;
        if let Node::Struct(ref mut s) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            s.doc_comment = doc_comment.or(s.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_class_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
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

    pub(super) fn parse_trait_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_trait()?;
        if let Node::Trait(ref mut t) = node {
            t.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_mixin_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_mixin()?;
        if let Node::Mixin(ref mut m) = node {
            m.doc_comment = doc_comment.or(m.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_mixin_with_attrs(&mut self, _attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        self.parse_mixin()
    }

    /// Parse a class/struct/enum alias: `alias NewName = OldName`
    ///
    /// # Syntax
    /// ```simple
    /// alias Point2D = Point
    /// alias Optional = Option
    ///
    /// @deprecated("Use Point2D instead")
    /// alias OldPoint = Point
    /// ```
    pub(crate) fn parse_class_alias(&mut self) -> Result<Node, ParseError> {
        self.parse_class_alias_with_decorators(vec![])
    }

    /// Parse a class alias with decorators
    pub(crate) fn parse_class_alias_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Alias)?;

        // Expect the new alias name (PascalCase identifier)
        let name = self.expect_identifier()?;

        self.expect(&TokenKind::Assign)?;

        // Expect the target type name
        let target = self.expect_identifier()?;

        Ok(Node::ClassAlias(ClassAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            target,
            visibility: Visibility::Private,
            decorators,
            doc_comment: None,
        }))
    }

    /// Parse a function alias: `fn new_name = old_name`
    ///
    /// This is called when we detect the pattern `fn name = target` instead of
    /// `fn name(...)`. The detection happens in parse_function_with_attrs.
    ///
    /// # Syntax
    /// ```simple
    /// fn println = print
    ///
    /// @deprecated("Use println instead")
    /// fn old_print = print
    /// ```
    pub(crate) fn parse_function_alias(&mut self) -> Result<Node, ParseError> {
        self.parse_function_alias_with_decorators(vec![])
    }

    /// Parse a function alias with decorators
    pub(crate) fn parse_function_alias_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Fn)?;

        // Expect the new alias name
        let name = self.expect_identifier()?;

        self.expect(&TokenKind::Assign)?;

        // Expect the target function name
        let target = self.expect_identifier()?;

        Ok(Node::FunctionAlias(FunctionAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            target,
            visibility: Visibility::Private,
            decorators,
            doc_comment: None,
        }))
    }
}
