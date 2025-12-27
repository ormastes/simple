//! Top-level item parsing
//!
//! This module handles parsing of public items and attributed items.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

impl<'a> Parser<'a> {
    pub(super) fn parse_pub_item_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function_with_doc(doc_comment)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function_with_doc(doc_comment)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct_with_doc(doc_comment)?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class_with_doc(doc_comment)?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum_with_doc(doc_comment)?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Union => {
                let mut node = self.parse_union_with_doc(doc_comment)?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait_with_doc(doc_comment)?;
                if let Node::Trait(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            _ => self.parse_pub_item(),
        }
    }

    pub(super) fn parse_pub_item(&mut self) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct()?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class()?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum()?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Union => {
                let mut node = self.parse_union()?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait()?;
                if let Node::Trait(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Actor => {
                let mut node = self.parse_actor()?;
                if let Node::Actor(ref mut a) = node {
                    a.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Const => {
                let mut node = self.parse_const()?;
                if let Node::Const(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Static => {
                let mut node = self.parse_static()?;
                if let Node::Static(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Type => {
                let mut node = self.parse_type_alias()?;
                if let Node::TypeAlias(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Unit => {
                let mut node = self.parse_unit()?;
                if let Node::Unit(ref mut u) = node {
                    u.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Extern => {
                let mut node = self.parse_extern()?;
                if let Node::Extern(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Macro => {
                let mut node = self.parse_macro_def()?;
                if let Node::Macro(ref mut m) = node {
                    m.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Public, vec![]),
            TokenKind::Use => {
                // pub use is equivalent to export use (re-export)
                let start_span = self.current.span;
                self.advance(); // consume 'use'
                let (path, target) = self.parse_use_path_and_target()?;
                Ok(Node::ExportUseStmt(ExportUseStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    path,
                    target,
                }))
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, trait, actor, const, static, type, extern, macro, or mod after 'pub'",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    pub(super) fn parse_attributed_item_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_attributed_item()?;
        // Set doc_comment on the parsed item
        match &mut node {
            Node::Function(f) => f.doc_comment = doc_comment,
            Node::Struct(s) => s.doc_comment = doc_comment,
            Node::Class(c) => c.doc_comment = doc_comment,
            Node::Enum(e) => e.doc_comment = doc_comment,
            Node::Trait(t) => t.doc_comment = doc_comment,
            _ => {}
        }
        Ok(node)
    }

    /// Parse an attributed item: #[attr] fn/struct/class/etc
    pub(super) fn parse_attributed_item(&mut self) -> Result<Node, ParseError> {
        let mut attributes = Vec::new();

        // Parse all attributes (can be multiple: #[a] #[b] fn foo)
        while self.check(&TokenKind::Hash) {
            attributes.push(self.parse_attribute()?);
            // Skip newlines between attributes
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the item with collected attributes
        // Could be function, struct, class, etc.
        match &self.current.kind {
            TokenKind::At => {
                // Attributes followed by decorators - extract effect decorators
                let mut decorators = Vec::new();
                let mut effects = Vec::new();
                while self.check(&TokenKind::At) {
                    let decorator = self.parse_decorator()?;

                    // Check if this is an effect decorator
                    if let Expr::Identifier(name) = &decorator.name {
                        if let Some(effect) = Effect::from_decorator_name(name) {
                            effects.push(effect);
                            while self.check(&TokenKind::Newline) {
                                self.advance();
                            }
                            continue;
                        }
                    }

                    decorators.push(decorator);
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                let mut node = self.parse_function_with_attrs(decorators, attributes)?;
                if let Node::Function(ref mut f) = node {
                    f.effects = effects;
                }
                Ok(node)
            }
            TokenKind::Fn => self.parse_function_with_attrs(vec![], attributes),
            TokenKind::Async => {
                self.advance();
                let mut func = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = func {
                    f.effects.push(Effect::Async);
                }
                Ok(func)
            }
            TokenKind::Struct => self.parse_struct_with_attrs(attributes),
            TokenKind::Class => self.parse_class_with_attrs(attributes),
            TokenKind::Enum => self.parse_enum_with_attrs(attributes),
            TokenKind::Union => self.parse_union_with_attrs(attributes),
            TokenKind::Impl => self.parse_impl_with_attrs(attributes),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_attrs(attributes)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Private, attributes),
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, union, impl, mod, or pub after attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    pub(super) fn parse_pub_item_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct_with_attrs(attributes)?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class_with_attrs(attributes)?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Mod => self.parse_mod(Visibility::Public, attributes),
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, or mod after pub with attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
