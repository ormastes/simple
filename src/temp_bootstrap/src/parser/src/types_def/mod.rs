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

        // Allow optional parent/mixin: struct Foo(Bar):
        if self.check(&TokenKind::LParen) {
            self.advance();
            let _parent = self.expect_identifier()?; // consume parent name (not stored in StructDef)
            self.expect(&TokenKind::RParen)?;
        }

        // Skip `with TraitA, TraitB, ...` clause (trait implementation list)
        if self.check(&TokenKind::With) {
            self.advance();
            self.expect_identifier()?;
            while self.check(&TokenKind::Comma) {
                self.advance();
                self.skip_whitespace_tokens();
                self.expect_identifier()?;
            }
        }

        let where_clause = self.parse_where_clause()?;

        // Handle unit struct (no body, no colon) - just a bare struct name
        if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            return Ok(Node::Struct(StructDef {
                span: self.make_span(start_span),
                name,
                generic_params,
                where_clause,
                fields: vec![],
                methods: vec![],
                visibility: Visibility::Private,
                attributes,
                doc_comment: None,
                invariant: None,
            }));
        }

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
        } else if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "extends") {
            // Handle `class Child extends Parent:` syntax
            self.advance(); // consume 'extends'
            let p = self.expect_identifier()?;
            Some(p)
        } else {
            None
        };

        // Skip `with TraitA, TraitB, ...` clause (trait implementation list)
        if self.check(&TokenKind::With) {
            self.advance();
            // Parse comma-separated trait names
            self.expect_identifier()?;
            while self.check(&TokenKind::Comma) {
                self.advance();
                self.skip_whitespace_tokens();
                self.expect_identifier()?;
            }
        }

        let where_clause = self.parse_where_clause()?;

        // Handle unit class (no body, no colon) - just a bare class name
        if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            return Ok(Node::Class(ClassDef {
                span: self.make_span(start_span),
                name,
                generic_params,
                where_clause,
                fields: vec![],
                methods: vec![],
                parent,
                visibility: Visibility::Private,
                attributes,
                doc_comment: None,
                invariant: None,
            }));
        }

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

    // === Mixin ===

    pub(crate) fn parse_mixin(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mixin)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let where_clause = self.parse_where_clause()?;

        // Handle unit mixin (no body)
        if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            return Ok(Node::Class(ClassDef {
                span: self.make_span(start_span),
                name,
                generic_params,
                where_clause,
                fields: vec![],
                methods: vec![],
                parent: None,
                visibility: Visibility::Private,
                attributes: vec![],
                doc_comment: None,
                invariant: None,
            }));
        }

        let (fields, methods, invariant) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Class(ClassDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            fields,
            methods,
            parent: None,
            visibility: Visibility::Private,
            attributes: vec![],
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

        // Handle unit enum (no body, no colon)
        if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            // Check if next is NOT an indent - unit enum
            if !self.check(&TokenKind::Indent) {
                return Ok(Node::Enum(EnumDef {
                    span: self.make_span(start_span),
                    name,
                    generic_params,
                    where_clause,
                    variants: vec![],
                    visibility: Visibility::Private,
                    attributes,
                    doc_comment: None,
                }));
            }
            // If there IS an indent, fall through to parse body (colon-less enum with body)
        } else {
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
        }

        if !self.check(&TokenKind::Indent) {
            // Empty body - return with empty variants
            return Ok(Node::Enum(EnumDef {
                span: self.make_span(start_span),
                name,
                generic_params,
                where_clause,
                variants: vec![],
                visibility: Visibility::Private,
                attributes,
                doc_comment: None,
            }));
        }
        self.expect(&TokenKind::Indent)?;

        // Parse enum body: variants + optional inline methods (fn/me/static/pub)
        let mut variants = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Skip doc comments
            if let TokenKind::DocComment(_) = &self.current.kind {
                self.advance();
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                continue;
            }

            // Check if this is a method (fn/me/static/pub/async/@/#) or pass statement
            if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Me)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::Static)
                || self.check(&TokenKind::Pub)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
            {
                // Skip inline methods - just parse and discard for now
                let _item = self.parse_item()?;
            } else if self.check(&TokenKind::PassDoNothing) || self.check(&TokenKind::PassDn)
                || self.check(&TokenKind::Pass) || self.check(&TokenKind::PassTodo)
            {
                self.advance();
            } else if self.check(&TokenKind::Comma) || self.check(&TokenKind::Pipe) {
                // Skip commas and pipes between variants on same line
                // e.g., Rax | Rbx | Rcx  or  I8, I16, I32
                self.advance();
            } else {
                // Parse as enum variant
                variants.push(self.parse_enum_variant()?);
                // Skip optional comma or pipe after variant (for inline separated variants)
                if self.check(&TokenKind::Comma) || self.check(&TokenKind::Pipe) {
                    self.advance();
                }
            }
        }
        self.consume_dedent();

        Ok(Node::Enum(EnumDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            variants,
            visibility: Visibility::Private,
            attributes,
            doc_comment: None,
        }))
    }

    pub(crate) fn parse_enum_variant(&mut self) -> Result<EnumVariant, ParseError> {
        // Skip doc comments before variant
        while let TokenKind::DocComment(_) = &self.current.kind {
            self.advance();
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }
        let start_span = self.current.span;
        let name = self.expect_identifier()?;

        let fields = if self.check(&TokenKind::LParen) {
            // Parse enum variant fields — can be either named (name: Type) or positional (Type)
            Some(self.parse_enum_variant_fields()?)
        } else if self.check(&TokenKind::LBrace) {
            // Parse struct-style enum variant: Variant { field: Type, ... }
            self.advance(); // consume '{'
            let mut types = Vec::new();
            self.skip_whitespace_tokens();
            while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                // Parse named field: name: Type
                let _field_name = self.expect_identifier()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                types.push(ty);
                self.skip_whitespace_tokens();
                if !self.check(&TokenKind::RBrace) {
                    if self.check(&TokenKind::Comma) {
                        self.advance();
                    }
                    self.skip_whitespace_tokens();
                }
            }
            self.expect(&TokenKind::RBrace)?;
            Some(types)
        } else {
            None
        };

        // Handle discriminant values: Variant = 1
        if self.check(&TokenKind::Assign) {
            self.advance();
            // Parse and discard the discriminant value expression
            let _discriminant = self.parse_expression()?;
        }

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(EnumVariant {
            span: self.make_span(start_span),
            name,
            fields,
        })
    }

    /// Parse enum variant fields: (Type1, Type2) or (name: Type1, name2: Type2)
    /// Named fields are parsed but the name is discarded (stored as just types)
    fn parse_enum_variant_fields(&mut self) -> Result<Vec<Type>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut types = Vec::new();

        // Skip whitespace after opening paren (for multi-line variant fields)
        self.skip_whitespace_tokens();

        while !self.check(&TokenKind::RParen) {
            // Check if this is a named field: identifier (or keyword-as-name) followed by ':'
            let is_named = {
                let is_name_token = matches!(
                    &self.current.kind,
                    TokenKind::Identifier(_)
                        | TokenKind::Context
                        | TokenKind::Type
                        | TokenKind::From
                        | TokenKind::To
                        | TokenKind::NotTo
                        | TokenKind::In
                        | TokenKind::As
                        | TokenKind::Result
                        | TokenKind::Out
                        | TokenKind::OutErr
                        | TokenKind::Loop
                        | TokenKind::Old
                        | TokenKind::Var
                        | TokenKind::Fn
                        | TokenKind::Let
                        | TokenKind::Struct
                        | TokenKind::Class
                        | TokenKind::Enum
                        | TokenKind::Trait
                        | TokenKind::Impl
                        | TokenKind::Extern
                        | TokenKind::Static
                        | TokenKind::Const
                        | TokenKind::Self_
                        | TokenKind::Async
                        | TokenKind::Await
                        | TokenKind::Yield
                        | TokenKind::Spawn
                        | TokenKind::Move
                        | TokenKind::Union
                        | TokenKind::Actor
                        | TokenKind::Macro
                        | TokenKind::With
                        | TokenKind::Shared
                        | TokenKind::Mut
                        | TokenKind::Unit
                        | TokenKind::Bitfield
                        | TokenKind::Alias
                        | TokenKind::New
                        | TokenKind::Pub
                        | TokenKind::Priv
                        | TokenKind::Common
                        | TokenKind::Auto
                        | TokenKind::Gpu
                        | TokenKind::Dyn
                        | TokenKind::Vec
                        | TokenKind::Mod
                        | TokenKind::Super
                        | TokenKind::Import
                        | TokenKind::Export
                        | TokenKind::Use
                        | TokenKind::Case
                        | TokenKind::Me
                );
                if is_name_token {
                    let next = self
                        .pending_token
                        .clone()
                        .unwrap_or_else(|| self.lexer.next_token());
                    self.pending_token = Some(next.clone());
                    next.kind == TokenKind::Colon
                } else {
                    false
                }
            };

            if is_named {
                self.advance(); // consume the name
                self.expect(&TokenKind::Colon)?; // consume ':'
            }

            types.push(self.parse_type()?);

            // Skip whitespace after type
            self.skip_whitespace_tokens();

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
                // Skip whitespace after comma
                self.skip_whitespace_tokens();
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(types)
    }

    // === Trait ===

    pub(crate) fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;

        // Handle supertrait constraint: trait Copy: Clone or trait Foo: Bar + Baz
        if self.check(&TokenKind::Colon) {
            // Peek to see if this is a supertrait (identifier after colon) or body block (newline after colon)
            let next = self.pending_token.clone()
                .unwrap_or_else(|| self.lexer.next_token());
            self.pending_token = Some(next.clone());
            if matches!(next.kind, TokenKind::Identifier(_) | TokenKind::Self_) {
                self.advance(); // consume ':'
                // Parse supertrait name(s)
                let _supertrait = self.expect_identifier()?;
                // Handle generic args on supertrait
                let _ = self.parse_generic_params();
                // Handle multiple supertraits with + separator
                while self.check(&TokenKind::Plus) {
                    self.advance();
                    let _next_supertrait = self.expect_identifier()?;
                    let _ = self.parse_generic_params();
                }
            }
        }

        let where_clause = self.parse_where_clause()?;

        // Handle unit trait (no body, no colon)
        if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            if !self.check(&TokenKind::Indent) {
                return Ok(Node::Trait(TraitDef {
                    span: self.make_span(start_span),
                    name,
                    generic_params,
                    where_clause,
                    methods: vec![],
                    visibility: Visibility::Private,
                    doc_comment: None,
                }));
            }
        }

        let methods = self.parse_indented_trait_methods()?;

        Ok(Node::Trait(TraitDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            methods,
            visibility: Visibility::Private,
            doc_comment: None,
        }))
    }

    // === Impl ===

    pub(crate) fn parse_impl(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        // Parse optional generic params for impl block: impl<T> Trait for Type<T>
        let generic_params = self.parse_generic_params()?;

        let first_name = self.expect_identifier()?;

        // Parse optional generic args after type name: impl Poll<T> or impl List[T]
        let _impl_type_args = if self.check(&TokenKind::Lt) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::Gt) && !self.is_at_end() {
                // Handle const generic: const N: usize
                if self.check(&TokenKind::Const) {
                    self.advance();
                    let _name = self.expect_identifier()?;
                    if self.check(&TokenKind::Colon) {
                        self.advance();
                        args.push(self.parse_type()?);
                    }
                } else {
                    let ty = self.parse_type()?;
                    // Handle associated type binding: Item=T
                    if self.check(&TokenKind::Assign) {
                        self.advance();
                        args.push(self.parse_type()?);
                    } else {
                        args.push(ty);
                    }
                }
                if !self.check(&TokenKind::Gt) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::Gt)?;
            args
        } else if self.check(&TokenKind::LBracket) {
            // Square bracket generics: impl List[T]:
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RBracket) && !self.is_at_end() {
                // Handle const generic: const N: usize
                if self.check(&TokenKind::Const) {
                    self.advance();
                    let _name = self.expect_identifier()?;
                    if self.check(&TokenKind::Colon) {
                        self.advance();
                        args.push(self.parse_type()?);
                    }
                } else {
                    let ty = self.parse_type()?;
                    // Handle associated type binding: Item=T
                    if self.check(&TokenKind::Assign) {
                        self.advance();
                        args.push(self.parse_type()?);
                    } else {
                        args.push(ty);
                    }
                }
                if !self.check(&TokenKind::RBracket) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RBracket)?;
            args
        } else {
            vec![]
        };

        let (trait_name, target_type) = if self.check(&TokenKind::For) {
            self.advance();
            let target = self.parse_type()?;
            (Some(first_name), target)
        } else {
            (None, Type::Simple(first_name))
        };

        let where_clause = self.parse_where_clause()?;

        // Handle unit impl (no body, no colon) - e.g., `impl Error for IndexError`
        let methods = if self.check(&TokenKind::Newline) || self.is_at_end() {
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
            if !self.check(&TokenKind::Indent) {
                vec![]
            } else {
                // Has indent after newline (implicit block without colon) - shouldn't happen normally
                // but handle gracefully
                self.parse_indented_methods()?
            }
        } else {
            self.parse_indented_methods()?
        };

        Ok(Node::Impl(ImplBlock {
            span: self.make_span(start_span),
            generic_params,
            target_type,
            trait_name,
            where_clause,
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

    /// Skip newline, indent, and dedent tokens (used inside delimiters like (), [], <>, {})
    pub(crate) fn skip_whitespace_tokens(&mut self) {
        while self.check(&TokenKind::Newline)
            || self.check(&TokenKind::Indent)
            || self.check(&TokenKind::Dedent)
        {
            self.advance();
        }
    }

    /// Peek ahead through Newline/Indent tokens to check if a binary operator follows.
    /// Returns true if after skipping Newline+Indent, one of the target tokens appears.
    /// Does NOT consume any tokens -- only peeks.
    pub(crate) fn peek_continuation_for_token(&mut self, targets: &[TokenKind]) -> bool {
        if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Indent) {
            return false;
        }

        // Save state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_token.clone();

        let first_from_pending = saved_pending.is_some();
        let mut lexer_tokens = Vec::new();

        // Advance past whitespace
        self.advance(); // consume first Newline/Indent
        if !first_from_pending {
            lexer_tokens.push(self.current.clone());
        }
        let mut found_indent = self.check(&TokenKind::Indent) || saved_current.kind == TokenKind::Indent;
        while self.check(&TokenKind::Indent) || self.check(&TokenKind::Newline) {
            if self.check(&TokenKind::Indent) {
                found_indent = true;
            }
            self.advance();
            lexer_tokens.push(self.current.clone());
        }

        // Check if current token matches any target
        let mut found = false;
        if found_indent {
            for target in targets {
                if std::mem::discriminant(&self.current.kind) == std::mem::discriminant(target) {
                    found = true;
                    break;
                }
            }
        }

        // Restore state
        let leftover_pending = self.pending_token.take();
        if let Some(lp) = leftover_pending {
            self.lexer.pending_tokens.push(lp);
        }
        for tok in lexer_tokens.into_iter().rev() {
            self.lexer.pending_tokens.push(tok);
        }
        self.current = saved_current;
        self.previous = saved_previous;
        self.pending_token = saved_pending;
        found
    }

    /// Skip whitespace tokens after a binary operator for multi-line expression continuation.
    /// Returns the net number of INDENT tokens consumed (minus DEDENTs), so the caller
    /// can consume matching DEDENTs after parsing the right operand.
    pub(crate) fn skip_whitespace_for_continuation(&mut self) -> usize {
        let mut indent_depth = 0usize;
        while self.check(&TokenKind::Newline)
            || self.check(&TokenKind::Indent)
            || self.check(&TokenKind::Dedent)
        {
            if self.check(&TokenKind::Indent) {
                indent_depth += 1;
            } else if self.check(&TokenKind::Dedent) {
                indent_depth = indent_depth.saturating_sub(1);
            }
            self.advance();
        }
        indent_depth
    }

    /// Consume N trailing DEDENT tokens (matching INDENTs consumed during expression continuation).
    /// Skips intervening Newline tokens as needed.
    pub(crate) fn consume_continuation_dedents(&mut self, count: usize) {
        for _ in 0..count {
            // Skip newlines before the dedent
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
        }
    }

    /// Consume dedent if present
    pub(crate) fn consume_dedent(&mut self) {
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }
    }

    /// Parse a colon-newline-indent sequence.
    /// Returns `true` if indent was found (body follows), `false` if no indent (empty body).
    fn expect_block_start(&mut self) -> Result<bool, ParseError> {
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        if !self.check(&TokenKind::Indent) {
            // Empty body - no indent after newline
            return Ok(false);
        }
        self.expect(&TokenKind::Indent)?;
        Ok(true)
    }

    /// Parse methods in an indented block (impl only - all methods must have bodies)
    fn parse_indented_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        if !self.expect_block_start()? {
            return Ok(vec![]);
        }
        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Skip doc comments
            if let TokenKind::DocComment(_) = &self.current.kind {
                self.advance();
                while self.check(&TokenKind::Newline) { self.advance(); }
                continue;
            }
            // Skip pass statements
            if self.check(&TokenKind::PassDoNothing) || self.check(&TokenKind::PassDn)
                || self.check(&TokenKind::Pass) || self.check(&TokenKind::PassTodo)
            {
                self.advance();
                continue;
            }
            // Handle static, pub, me, async, decorators
            if self.check(&TokenKind::Static) {
                self.advance(); // consume 'static'
            }
            if self.check(&TokenKind::Pub) {
                self.advance(); // consume 'pub'
                if self.check(&TokenKind::Static) { self.advance(); }
            }
            if self.check(&TokenKind::Me) || self.check(&TokenKind::Async) || self.check(&TokenKind::At) || self.check(&TokenKind::Hash) {
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else if self.check(&TokenKind::Var) || self.check(&TokenKind::Let) || self.check(&TokenKind::Extern) || self.check(&TokenKind::Const) {
                // Allow var/let/extern/const declarations inside impl blocks (skip them for now)
                let _item = self.parse_item()?;
            } else if self.check(&TokenKind::Fn) {
                let item = self.parse_function()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else {
                // Unknown token in impl body - try to parse as item and skip
                let _item = self.parse_item()?;
            }
        }
        self.consume_dedent();
        Ok(methods)
    }

    /// Parse trait methods in an indented block (can be abstract or have default impl)
    fn parse_indented_trait_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        if !self.expect_block_start()? {
            return Ok(vec![]);
        }
        let mut methods = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Skip doc comments
            if let TokenKind::DocComment(_) = &self.current.kind {
                self.advance();
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                continue;
            }
            // Skip pass statements
            if self.check(&TokenKind::PassDoNothing) || self.check(&TokenKind::PassDn)
                || self.check(&TokenKind::Pass) || self.check(&TokenKind::PassTodo)
            {
                self.advance();
                continue;
            }
            // Handle static fn, me, pub fn, async fn, etc.
            if self.check(&TokenKind::Static) {
                self.advance(); // consume 'static'
            }
            if self.check(&TokenKind::Pub) {
                self.advance(); // consume 'pub'
                if self.check(&TokenKind::Static) {
                    self.advance(); // consume 'static'
                }
            }
            if self.check(&TokenKind::Me) {
                // me method -> parse as trait me method (may be abstract)
                methods.push(self.parse_trait_me_method()?);
            } else if self.check(&TokenKind::Fn) {
                methods.push(self.parse_trait_method()?);
            } else if self.check(&TokenKind::Let) || self.check(&TokenKind::Var)
                || self.check(&TokenKind::Extern) || self.check(&TokenKind::Const)
            {
                // val/var/extern/const inside trait - skip
                let _item = self.parse_item()?;
            } else {
                // Unknown - try to parse as item
                let _item = self.parse_item()?;
            }
        }
        self.consume_dedent();
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
            effect: None,
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract,
        })
    }

    /// Parse a trait `me` method (can be abstract or have default implementation)
    /// Abstract: `me foo(x: i64) -> i64` (ends with newline)
    /// Default:  `me foo(x: i64) -> i64:\n    ...`
    fn parse_trait_me_method(&mut self) -> Result<FunctionDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Me)?;

        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params()?;
        let mut params = self.parse_parameters()?;

        // Add implicit mutable self as first parameter
        params.insert(
            0,
            Parameter {
                span: start_span,
                name: "self".to_string(),
                ty: None,
                default: None,
                mutability: Mutability::Mutable,
            },
        );

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
            effect: None,
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract,
        })
    }

    /// Parse fields and methods in an indented block (class, actor, struct)
    fn parse_indented_fields_and_methods(
        &mut self,
    ) -> Result<(Vec<Field>, Vec<FunctionDef>, Option<InvariantBlock>), ParseError> {
        if !self.expect_block_start()? {
            return Ok((vec![], vec![], None));
        }
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut invariant = None;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Skip doc comments
            if let TokenKind::DocComment(_) = &self.current.kind {
                self.advance();
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                continue;
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
                || self.check(&TokenKind::Me)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
            {
                // Method: fn/me/async fn/decorated method
                let item = self.parse_item()?;
                if let Node::Function(f) = item {
                    methods.push(f);
                }
            } else if self.check(&TokenKind::Static) {
                // Static method: static fn method_name(...)
                self.advance(); // consume 'static'
                let mut item = self.parse_item()?;
                if let Node::Function(ref mut f) = item {
                    methods.push(f.clone());
                }
            } else if self.check(&TokenKind::Pub) {
                // Public item: pub fn/me/static/field
                // Check if next token after 'pub' is a method keyword
                let is_pub_method = {
                    let next = self
                        .pending_token
                        .clone()
                        .unwrap_or_else(|| self.lexer.next_token());
                    self.pending_token = Some(next.clone());
                    matches!(next.kind,
                        TokenKind::Fn | TokenKind::Me | TokenKind::Static
                        | TokenKind::Async | TokenKind::At | TokenKind::Hash
                        | TokenKind::Extern | TokenKind::Const
                        | TokenKind::Struct | TokenKind::Class | TokenKind::Enum
                        | TokenKind::Trait | TokenKind::Impl | TokenKind::Union
                    )
                };
                if is_pub_method {
                    let item = self.parse_item()?;
                    match item {
                        Node::Function(f) => methods.push(f),
                        _ => {}
                    }
                } else {
                    // pub field_name: Type — parse as field (parse_field handles pub)
                    fields.push(self.parse_field()?);
                }
            } else if self.check(&TokenKind::Let)
                || self.check(&TokenKind::Extern) || self.check(&TokenKind::Const)
            {
                // val/let/extern/const declarations inside class/struct bodies
                // Parse as items and skip (they're type-level bindings)
                let _item = self.parse_item()?;
            } else if self.check(&TokenKind::Var) {
                // var declarations - could be a field declared with 'var' for mutability
                // Also handle `var fn method_name(...)` as mutable method
                let next = self
                    .pending_token
                    .clone()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next.clone());
                if next.kind == TokenKind::Fn || next.kind == TokenKind::Async {
                    // `var fn ...` — mutable method, treat like `me fn ...`
                    self.advance(); // consume 'var'
                    let item = self.parse_item()?;
                    if let Node::Function(f) = item {
                        methods.push(f);
                    }
                } else {
                    // regular var declaration
                    let _item = self.parse_item()?;
                }
            } else if self.check(&TokenKind::Impl) {
                // `impl TraitName` inside class body — skip the impl declaration
                self.advance(); // consume 'impl'
                // Skip the trait name (may be a dotted path)
                if matches!(&self.current.kind, TokenKind::Identifier(_)) {
                    self.advance();
                    while self.check(&TokenKind::Dot) {
                        self.advance();
                        if matches!(&self.current.kind, TokenKind::Identifier(_)) {
                            self.advance();
                        }
                    }
                    // Skip optional generic params
                    let _ = self.parse_generic_params();
                }
            } else if self.check(&TokenKind::Trait) {
                // `trait TraitName` inside class body — skip trait declaration line
                self.advance(); // consume 'trait'
                if matches!(&self.current.kind, TokenKind::Identifier(_)) {
                    self.advance();
                }
            } else if self.check(&TokenKind::Use) || self.check(&TokenKind::Import) {
                // `use MixinName` or `use module.path` inside class body — skip
                let _item = self.parse_item()?;
            } else if self.check(&TokenKind::Macro) {
                // macro inside class body — parse as item
                let _item = self.parse_item()?;
            } else if self.check(&TokenKind::PassDoNothing) || self.check(&TokenKind::PassDn)
                || self.check(&TokenKind::Pass) || self.check(&TokenKind::PassTodo)
            {
                self.advance();
            } else {
                // Field (may be public: pub field_name: Type)
                fields.push(self.parse_field()?);
            }
        }
        self.consume_dedent();
        Ok((fields, methods, invariant))
    }
}
