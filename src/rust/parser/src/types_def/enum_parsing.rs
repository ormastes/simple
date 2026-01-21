// Enum and Union parsing
//
// This module handles:
// - Enum definition parsing
// - Union definition parsing (alias for enum with data variants)
// - Enum variant parsing
// - Enum field list parsing

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::super::Parser;

impl<'a> Parser<'a> {
    // === Enum ===

    pub(crate) fn parse_enum(&mut self) -> Result<Node, ParseError> {
        self.parse_enum_with_attrs(vec![])
    }

    pub(crate) fn parse_enum_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Enum)?;
        self.parse_enum_body(start_span, attributes)
    }

    // === Union (alias for enum with data variants) ===

    pub(crate) fn parse_union(&mut self) -> Result<Node, ParseError> {
        self.parse_union_with_attrs(vec![])
    }

    pub(crate) fn parse_union_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Union)?;
        self.parse_enum_body(start_span, attributes)
    }

    /// Shared parsing logic for enum and union bodies
    fn parse_enum_body(&mut self, start_span: Span, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;
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
    fn parse_enum_variants_and_methods(&mut self) -> Result<(Vec<EnumVariant>, Vec<FunctionDef>), ParseError> {
        self.debug_enter("parse_enum_variants_and_methods");
        let mut variants = Vec::new();
        let mut methods = Vec::new();
        let mut iterations = 0usize;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_enum_variants_and_methods")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            // Check if this is a method definition
            if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || (self.check(&TokenKind::Pub) && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async)))
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
        self.debug_exit("parse_enum_variants_and_methods");
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
            let field = if matches!(self.current.kind, TokenKind::Identifier { .. }) {
                // Save position for potential backtrack
                let saved_current = self.current.clone();

                // Try to get the identifier
                if let TokenKind::Identifier { name: ident, .. } = &self.current.kind {
                    let name = ident.clone();
                    self.advance();

                    if self.check(&TokenKind::Colon) {
                        // This is a named field: `name: Type`
                        self.advance();
                        let ty = self.parse_type()?;
                        EnumField { name: Some(name), ty }
                    } else {
                        // Not a named field, backtrack and parse as type
                        // Restore position (put current token back)
                        self.pending_tokens.push_front(self.current.clone());
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
}
