// Enum and Union parsing
//
// This module handles:
// - Enum definition parsing
// - Union definition parsing (alias for enum with data variants)
// - Enum variant parsing
// - Enum field list parsing

use std::collections::HashMap;

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

    /// Parse enum body without consuming the keyword (for `effect` alias)
    pub(crate) fn parse_enum_body_after_keyword(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.parse_enum_body(start_span, vec![])
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

        // Handle optional docstring after indent
        let mut doc_comment = None;
        self.skip_newlines();
        match &self.current.kind {
            TokenKind::String(content) => {
                doc_comment = Some(DocComment {
                    content: content.clone(),
                });
                self.advance();
                self.skip_newlines();
            }
            TokenKind::FString(parts) => {
                // Extract text from FStringToken parts for doc comment
                use crate::token::FStringToken;
                let content: String = parts
                    .iter()
                    .filter_map(|p| match p {
                        FStringToken::Literal(s) => Some(s.clone()),
                        FStringToken::Expr(_) => None, // Skip interpolated expressions
                    })
                    .collect();
                doc_comment = Some(DocComment { content });
                self.advance();
                self.skip_newlines();
            }
            _ => {}
        }

        let (variants, methods) = self.parse_enum_variants_and_methods()?;

        Ok(Node::Enum(EnumDef {
            span: self.make_span(start_span),
            name,
            generic_params: generic_params.clone(),
            where_clause,
            variants,
            methods,
            visibility: Visibility::Private,
            attributes,
            doc_comment,
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
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
                // Parse enum variant(s) - may be comma-separated on same line
                variants.push(self.parse_enum_variant()?);
                // Handle comma-separated or pipe-separated variants on the same line:
                //   Add, Sub, Mul       (comma)
                //   Rax | Rbx | Rcx     (pipe)
                while self.check(&TokenKind::Comma) || self.check(&TokenKind::Pipe) {
                    self.advance();
                    // If we hit newline/indent/dedent after separator, stop
                    if self.check(&TokenKind::Newline)
                        || self.check(&TokenKind::Indent)
                        || self.check(&TokenKind::Dedent)
                        || self.is_at_end()
                    {
                        break;
                    }
                    // Parse next variant in the separated list
                    variants.push(self.parse_enum_variant()?);
                }
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
            // Tuple-style variant: Variant(Type1, Type2)
            Some(self.parse_enum_field_list()?)
        } else if self.check(&TokenKind::LBrace) {
            // Struct-style variant: Variant { field1: Type1, field2: Type2 }
            Some(self.parse_enum_struct_fields()?)
        } else {
            None
        };

        // Check for discriminant value: Variant = 0
        let discriminant = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // Note: Don't consume newline here - let the caller handle it
        // This allows comma-separated variants: Add, Sub, Mul

        Ok(EnumVariant {
            span: self.make_span(start_span),
            name,
            fields,
            discriminant,
        })
    }

    /// Parse struct-style enum variant fields: `{ name1: Type1, name2: Type2 }`
    fn parse_enum_struct_fields(&mut self) -> Result<Vec<EnumField>, ParseError> {
        self.expect(&TokenKind::LBrace)?;
        let mut fields = Vec::new();

        // Skip newlines after opening brace
        self.skip_newlines();

        while !self.check(&TokenKind::RBrace) {
            // Parse named field: `name: Type`
            let field_name = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            let field_type = self.parse_type()?;

            fields.push(EnumField {
                name: Some(field_name),
                ty: field_type,
            });

            // Skip comma and newlines between fields
            if self.check(&TokenKind::Comma) {
                self.advance();
                self.skip_newlines();
            } else if self.check(&TokenKind::Newline) {
                self.skip_newlines();
            }
        }

        self.expect(&TokenKind::RBrace)?;
        Ok(fields)
    }

    /// Parse enum variant fields: `(Type1, Type2)` or `(name1: Type1, name2: Type2)`
    /// Supports both positional and named fields.
    fn parse_enum_field_list(&mut self) -> Result<Vec<EnumField>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut fields = Vec::new();

        // Skip newlines after opening paren (for multi-line variant definitions)
        self.skip_newlines();

        while !self.check(&TokenKind::RParen) {
            // Try to parse as named field: `name: Type`
            // Look ahead to check if this is `Identifier/Keyword Colon Type`
            // Support keywords as field names (e.g., bounds, default, type)
            let maybe_name = match &self.current.kind {
                TokenKind::Identifier { name, .. } => Some(name.clone()),
                // Allow keywords as field names
                TokenKind::Type => Some("type".to_string()),
                TokenKind::Default => Some("default".to_string()),
                TokenKind::Result => Some("result".to_string()),
                TokenKind::Bounds => Some("bounds".to_string()),
                TokenKind::Alias => Some("alias".to_string()),
                TokenKind::From => Some("from".to_string()),
                TokenKind::To => Some("to".to_string()),
                TokenKind::In => Some("in".to_string()),
                TokenKind::Is => Some("is".to_string()),
                TokenKind::As => Some("as".to_string()),
                TokenKind::Match => Some("match".to_string()),
                TokenKind::Use => Some("use".to_string()),
                TokenKind::Unit => Some("unit".to_string()),
                TokenKind::Out => Some("out".to_string()),
                TokenKind::OutErr => Some("out_err".to_string()),
                TokenKind::Loop => Some("loop".to_string()),
                TokenKind::Sync => Some("sync".to_string()),
                TokenKind::Async => Some("async".to_string()),
                TokenKind::Kernel => Some("kernel".to_string()),
                TokenKind::Val => Some("val".to_string()),
                TokenKind::Literal => Some("literal".to_string()),
                TokenKind::Repr => Some("repr".to_string()),
                TokenKind::Extern => Some("extern".to_string()),
                TokenKind::Static => Some("static".to_string()),
                TokenKind::Const => Some("const".to_string()),
                TokenKind::Shared => Some("shared".to_string()),
                TokenKind::Gpu => Some("gpu".to_string()),
                TokenKind::Vec => Some("vec".to_string()),
                TokenKind::Context => Some("context".to_string()),
                TokenKind::New => Some("new".to_string()),
                TokenKind::Old => Some("old".to_string()),
                TokenKind::Var => Some("var".to_string()),
                TokenKind::Then => Some("then".to_string()),
                TokenKind::Else => Some("else".to_string()),
                TokenKind::Exists => Some("exists".to_string()),
                TokenKind::Gen => Some("gen".to_string()),
                TokenKind::Impl => Some("impl".to_string()),
                _ => None,
            };

            let field = if let Some(name) = maybe_name {
                // Save position for potential backtrack
                let saved_current = self.current.clone();
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
                // Not an identifier or keyword, just parse as type
                let ty = self.parse_type()?;
                EnumField { name: None, ty }
            };

            fields.push(field);

            // Skip newlines after field (for multi-line variant definitions)
            self.skip_newlines();

            // Handle comma or closing paren
            if self.check(&TokenKind::Comma) {
                self.advance(); // consume comma
                                // Skip newlines after comma
                self.skip_newlines();
            } else if !self.check(&TokenKind::RParen) {
                // Not comma and not RParen - error
                return Err(ParseError::unexpected_token(
                    "Comma",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(fields)
    }
}
