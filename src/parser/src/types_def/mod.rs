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
        self.parse_struct_with_attrs(vec![])
    }

    pub(crate) fn parse_struct_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let where_clause = self.parse_where_clause()?;
        // Parse fields, optional inline methods, and optional invariant
        let (fields, methods, invariant) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Struct(StructDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            fields,
            methods,
            visibility: Visibility::Private,
            attributes,
            doc_comment: None,
            invariant,
        }))
    }

    // === Class ===

    pub(crate) fn parse_class(&mut self) -> Result<Node, ParseError> {
        self.parse_class_with_attrs(vec![])
    }

    pub(crate) fn parse_class_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Class)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;

        let parent = if self.check(&TokenKind::LParen) {
            self.advance();
            let p = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(p)
        } else {
            None
        };

        let where_clause = self.parse_where_clause()?;
        let (fields, methods, invariant) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Class(ClassDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            fields,
            methods,
            parent,
            visibility: Visibility::Private,
            attributes,
            doc_comment: None,
            invariant,
        }))
    }

    // === Enum ===

    pub(crate) fn parse_enum(&mut self) -> Result<Node, ParseError> {
        self.parse_enum_with_attrs(vec![])
    }

    pub(crate) fn parse_enum_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Enum)?;
        self.parse_enum_body(start_span, attributes)
    }

    // === Union (alias for enum with data variants) ===

    pub(crate) fn parse_union(&mut self) -> Result<Node, ParseError> {
        self.parse_union_with_attrs(vec![])
    }

    pub(crate) fn parse_union_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Union)?;
        self.parse_enum_body(start_span, attributes)
    }

    /// Shared parsing logic for enum and union bodies
    fn parse_enum_body(
        &mut self,
        start_span: Span,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let where_clause = self.parse_where_clause()?;

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let (variants, methods) = self.parse_enum_variants_and_methods()?;

        Ok(Node::Enum(EnumDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            variants,
            methods,
            visibility: Visibility::Private,
            attributes,
            doc_comment: None,
        }))
    }

    /// Parse enum body: variants and optional methods
    fn parse_enum_variants_and_methods(
        &mut self,
    ) -> Result<(Vec<EnumVariant>, Vec<FunctionDef>), ParseError> {
        let mut variants = Vec::new();
        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Check if this is a method definition
            if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || (self.check(&TokenKind::Pub)
                    && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async)))
            {
                // Parse method
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                } else {
                    return Err(ParseError::syntax_error_with_span(
                        "Expected method definition in enum body",
                        self.current.span,
                    ));
                }
            } else {
                // Parse enum variant
                variants.push(self.parse_enum_variant()?);
            }
        }

        self.consume_dedent();
        Ok((variants, methods))
    }

    pub(crate) fn parse_enum_variant(&mut self) -> Result<EnumVariant, ParseError> {
        let start_span = self.current.span;
        let name = self.expect_identifier()?;

        let fields = if self.check(&TokenKind::LParen) {
            Some(self.parse_enum_field_list()?)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(EnumVariant {
            span: self.make_span(start_span),
            name,
            fields,
        })
    }

    /// Parse enum variant fields: `(Type1, Type2)` or `(name1: Type1, name2: Type2)`
    /// Supports both positional and named fields.
    fn parse_enum_field_list(&mut self) -> Result<Vec<EnumField>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut fields = Vec::new();

        while !self.check(&TokenKind::RParen) {
            // Try to parse as named field: `name: Type`
            // Look ahead to check if this is `Identifier Colon Type`
            let field = if matches!(self.current.kind, TokenKind::Identifier(_)) {
                // Save position for potential backtrack
                let saved_current = self.current.clone();

                // Try to get the identifier
                if let TokenKind::Identifier(ident) = &self.current.kind {
                    let name = ident.clone();
                    self.advance();

                    if self.check(&TokenKind::Colon) {
                        // This is a named field: `name: Type`
                        self.advance();
                        let ty = self.parse_type()?;
                        EnumField {
                            name: Some(name),
                            ty,
                        }
                    } else {
                        // Not a named field, backtrack and parse as type
                        // Restore position (put current token back)
                        self.pending_token = Some(self.current.clone());
                        self.current = saved_current;
                        let ty = self.parse_type()?;
                        EnumField { name: None, ty }
                    }
                } else {
                    // Should not happen, but handle gracefully
                    let ty = self.parse_type()?;
                    EnumField { name: None, ty }
                }
            } else {
                // Not an identifier, just parse as type
                let ty = self.parse_type()?;
                EnumField { name: None, ty }
            };

            fields.push(field);

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(fields)
    }

    // === Trait ===

    pub(crate) fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let where_clause = self.parse_where_clause()?;

        let (associated_types, methods) = self.parse_indented_trait_body()?;

        Ok(Node::Trait(TraitDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            associated_types,
            methods,
            visibility: Visibility::Private,
            doc_comment: None,
        }))
    }

    // === Impl ===

    pub(crate) fn parse_impl(&mut self) -> Result<Node, ParseError> {
        self.parse_impl_with_attrs(Vec::new())
    }

    pub(crate) fn parse_impl_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        // Parse optional generic params for impl block: impl<T> Trait for Type<T>
        let generic_params = self.parse_generic_params()?;

        let first_name = self.expect_identifier()?;

        let (trait_name, target_type) = if self.check(&TokenKind::For) {
            self.advance();
            let target = self.parse_type()?;
            (Some(first_name), target)
        } else {
            (None, Type::Simple(first_name))
        };

        let where_clause = self.parse_where_clause()?;
        let (associated_types, methods) = self.parse_indented_impl_body()?;

        Ok(Node::Impl(ImplBlock {
            span: self.make_span(start_span),
            attributes,
            generic_params,
            target_type,
            trait_name,
            where_clause,
            associated_types,
            methods,
        }))
    }

    // === Actor ===

    pub(crate) fn parse_actor(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Actor)?;
        let name = self.expect_identifier()?;

        let (fields, methods, _invariant) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Actor(ActorDef {
            span: self.make_span(start_span),
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
            span: self.make_span(start_span),
            name,
            ty,
            default,
            mutability,
            visibility,
        })
    }

    // === Helper methods to reduce duplication ===

    /// Create a span from start_span to the current position
    fn make_span(&self, start_span: Span) -> Span {
        Span::new(
            start_span.start,
            self.previous.span.end,
            start_span.line,
            start_span.column,
        )
    }

    /// Skip newlines until we hit a non-newline token
    pub(crate) fn skip_newlines(&mut self) {
        while self.check(&TokenKind::Newline) {
            self.advance();
        }
    }

    /// Consume dedent if present
    fn consume_dedent(&mut self) {
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }
    }

    /// Parse a colon-newline-indent sequence
    fn expect_block_start(&mut self) -> Result<(), ParseError> {
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        Ok(())
    }

    /// Parse indented items with a custom parser function
    fn parse_indented_items<T, F>(&mut self, mut parse_item: F) -> Result<Vec<T>, ParseError>
    where
        F: FnMut(&mut Self) -> Result<T, ParseError>,
    {
        let mut items = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            items.push(parse_item(self)?);
        }
        self.consume_dedent();
        Ok(items)
    }

    /// Parse fields in an indented block (struct)
    fn parse_indented_fields(&mut self) -> Result<Vec<Field>, ParseError> {
        self.expect_block_start()?;
        self.parse_indented_items(|p| p.parse_field())
    }

    /// Parse methods in an indented block (impl only - all methods must have bodies)
    /// Parse impl body: associated type implementations and methods
    fn parse_indented_impl_body(&mut self) -> Result<(Vec<AssociatedTypeImpl>, Vec<FunctionDef>), ParseError> {
        self.expect_block_start()?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Check for associated type impl: `type Item = i64`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_impl()?);
            } else {
                // Handle optional `pub` visibility prefix for methods
                let visibility = if self.check(&TokenKind::Pub) {
                    self.advance();
                    crate::ast::Visibility::Public
                } else {
                    crate::ast::Visibility::Private
                };
                let item = self.parse_function()?;
                if let Node::Function(mut f) = item {
                    f.visibility = visibility;
                    methods.push(f);
                }
            }
        }
        self.consume_dedent();
        Ok((associated_types, methods))
    }

    /// Parse associated type implementation in an impl block
    /// `type Item = i64`
    fn parse_associated_type_impl(&mut self) -> Result<AssociatedTypeImpl, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        // Consume newline
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(AssociatedTypeImpl {
            span: self.make_span(start_span),
            name,
            ty,
        })
    }

    /// Parse methods only (legacy)
    fn parse_indented_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        let (_, methods) = self.parse_indented_impl_body()?;
        Ok(methods)
    }

    /// Parse trait body: associated types and methods
    fn parse_indented_trait_body(&mut self) -> Result<(Vec<AssociatedTypeDef>, Vec<FunctionDef>), ParseError> {
        self.expect_block_start()?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Check for associated type: `type Name` or `type Name: Bound` or `type Name = Default`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_def()?);
            } else {
                methods.push(self.parse_trait_method()?);
            }
        }
        self.consume_dedent();
        Ok((associated_types, methods))
    }

    /// Parse associated type declaration in a trait
    /// `type Item` or `type Item: Clone` or `type Item = i64`
    fn parse_associated_type_def(&mut self) -> Result<AssociatedTypeDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;
        let name = self.expect_identifier()?;

        // Parse optional bounds: `type Item: Clone + Default`
        let bounds = if self.check(&TokenKind::Colon) {
            self.advance();
            let mut bounds = Vec::new();
            bounds.push(self.expect_identifier()?);
            while self.check(&TokenKind::Plus) {
                self.advance();
                bounds.push(self.expect_identifier()?);
            }
            bounds
        } else {
            Vec::new()
        };

        // Parse optional default: `type Item = i64`
        let default = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Consume newline
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(AssociatedTypeDef {
            span: self.make_span(start_span),
            name,
            bounds,
            default,
        })
    }

    /// Parse trait methods in an indented block (can be abstract or have default impl)
    /// Legacy function for backwards compatibility
    fn parse_indented_trait_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        let (_, methods) = self.parse_indented_trait_body()?;
        Ok(methods)
    }

    /// Parse a single trait method (can be abstract or have default implementation)
    /// Abstract: `fn foo(self) -> i64` (ends with newline)
    /// Default:  `fn foo(self) -> i64:\n    return 0`
    fn parse_trait_method(&mut self) -> Result<FunctionDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_where_clause()?;

        // Check if this is an abstract method (newline) or has default body (colon)
        let (body, is_abstract) = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
            // Abstract method - no body
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            (Block::default(), true)
        } else {
            // Default implementation - has body
            self.expect(&TokenKind::Colon)?;
            (self.parse_block()?, false)
        };

        Ok(FunctionDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            params,
            return_type,
            where_clause,
            body,
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract,
            bounds_block: None,
        })
    }

    /// Parse fields and methods in an indented block (class, actor, struct)
    fn parse_indented_fields_and_methods(
        &mut self,
    ) -> Result<(Vec<Field>, Vec<FunctionDef>, Option<InvariantBlock>), ParseError> {
        self.expect_block_start()?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut invariant = None;

        // Skip docstring if present (first item after indent)
        self.skip_newlines();
        if matches!(self.current.kind, TokenKind::String(_)) {
            // This is a docstring, skip it for now (we don't store class-level docstrings)
            // TODO: Store this as class.doc_comment
            self.advance();
            self.skip_newlines();
        }

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Invariant) {
                // Parse invariant block (only one allowed)
                if invariant.is_some() {
                    return Err(ParseError::syntax_error_with_span(
                        "Multiple invariant blocks not allowed",
                        self.current.span,
                    ));
                }
                invariant = self.parse_invariant_block()?;
            } else if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || (self.check(&TokenKind::Pub)
                    && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async)))
            {
                // Method (optionally async/decorated/attributed/pub).
                let start_span = self.current.span;
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                } else {
                    return Err(ParseError::syntax_error_with_span(
                        "Expected method definition in class body",
                        start_span,
                    ));
                }
            } else {
                // Field (may be public: pub field_name: Type)
                fields.push(self.parse_field()?);
            }
        }
        self.consume_dedent();
        Ok((fields, methods, invariant))
    }
}
