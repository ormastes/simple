//! Type definition parsing module
//!
//! This module contains parsing logic for type definitions:
//! - struct
//! - class
//! - enum
//! - trait
//! - impl
//! - actor

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::Parser;

impl<'a> Parser<'a> {
    // === Struct ===

    pub(crate) fn parse_struct(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: struct Foo<T, U>:
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            fields.push(self.parse_field()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Struct(StructDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            fields,
            visibility: Visibility::Private,
            attributes: vec![],
        }))
    }

    pub(crate) fn parse_struct_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: struct Foo<T, U>:
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            fields.push(self.parse_field()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Struct(StructDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            fields,
            visibility: Visibility::Private,
            attributes,
        }))
    }

    // === Class ===

    pub(crate) fn parse_class(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Class)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: class Foo<T, U>
        let generic_params = self.parse_generic_params()?;

        let parent = if self.check(&TokenKind::LParen) {
            self.advance();
            let p = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(p)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Pub) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                fields.push(self.parse_field()?);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Class(ClassDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            fields,
            methods,
            parent,
            visibility: Visibility::Private,
            attributes: vec![],
        }))
    }

    pub(crate) fn parse_class_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Class)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: class Foo<T, U>
        let generic_params = self.parse_generic_params()?;

        let parent = if self.check(&TokenKind::LParen) {
            self.advance();
            let p = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(p)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Pub) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                fields.push(self.parse_field()?);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Class(ClassDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            fields,
            methods,
            parent,
            visibility: Visibility::Private,
            attributes,
        }))
    }

    // === Enum ===

    pub(crate) fn parse_enum(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Enum)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: enum Result<T, E>
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut variants = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            variants.push(self.parse_enum_variant()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Enum(EnumDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            variants,
            visibility: Visibility::Private,
            attributes: vec![],
        }))
    }

    pub(crate) fn parse_enum_with_attrs(
        &mut self,
        attrs: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_enum()?;
        if let Node::Enum(ref mut e) = node {
            e.attributes = attrs;
        }
        Ok(node)
    }

    pub(crate) fn parse_enum_variant(&mut self) -> Result<EnumVariant, ParseError> {
        let start_span = self.current.span;
        let name = self.expect_identifier()?;

        let fields = if self.check(&TokenKind::LParen) {
            self.advance();
            let mut types = Vec::new();
            while !self.check(&TokenKind::RParen) {
                types.push(self.parse_type()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Some(types)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(EnumVariant {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            fields,
        })
    }

    // === Trait ===

    pub(crate) fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        // Parse optional generic parameters: trait Foo<T>
        let generic_params = self.parse_generic_params()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            let item = self.parse_function()?;
            if let Node::Function(f) = item {
                methods.push(f);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Trait(TraitDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            methods,
            visibility: Visibility::Private,
        }))
    }

    // === Impl ===

    pub(crate) fn parse_impl(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        let first_name = self.expect_identifier()?;

        let (trait_name, target_type) = if self.check(&TokenKind::For) {
            self.advance();
            let target = self.parse_type()?;
            (Some(first_name), target)
        } else {
            (None, Type::Simple(first_name))
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            let item = self.parse_function()?;
            if let Node::Function(f) = item {
                methods.push(f);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Impl(ImplBlock {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            target_type,
            trait_name,
            methods,
        }))
    }

    // === Actor ===

    pub(crate) fn parse_actor(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Actor)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Pub) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                fields.push(self.parse_field()?);
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Actor(ActorDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            fields,
            methods,
            visibility: Visibility::Private,
        }))
    }

    // === Field (shared by struct, class, actor) ===

    pub(crate) fn parse_field(&mut self) -> Result<Field, ParseError> {
        let start_span = self.current.span;

        let visibility = if self.check(&TokenKind::Pub) {
            self.advance();
            Visibility::Public
        } else {
            Visibility::Private
        };

        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let default = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(Field {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
            default,
            mutability,
            visibility,
        })
    }
}
