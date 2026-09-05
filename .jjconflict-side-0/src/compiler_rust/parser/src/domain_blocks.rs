//! Domain-specific block parser (FR-COMPILER-005)
//!
//! Parses `schema`, `style`, `ui`, `music`, `bim`, `city`, `cad`, and `rtl`
//! block declarations into [`DomainBlockDef`] AST nodes.
//!
//! Syntax:
//! ```simple
//! schema MyModel:
//!     id: Uuid
//!     name: text
//!
//! style Button:
//!     color: text
//!     font_size: i32
//! ```
//!
//! Each domain block lowers to a struct with domain-specific metadata.
//! Domain-specific field validation is deferred to later compiler passes.
//!
//! # Lexer interaction
//!
//! `try_scan_custom_block` in `lexer/identifiers.rs` runs **before** keyword
//! matching in `scan_identifier`. When a domain word is immediately followed
//! by `{`, it is already consumed as a `CustomBlock` (raw payload form) and
//! these parser functions are never reached. The keyword tokens (e.g.
//! `TokenKind::Schema`) are only emitted when the word is **not** followed
//! directly by `{`.

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    // -----------------------------------------------------------------------
    // Public entry points — one per domain keyword
    // -----------------------------------------------------------------------

    pub(crate) fn parse_schema_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Schema)
    }

    pub(crate) fn parse_style_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Style)
    }

    pub(crate) fn parse_ui_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Ui)
    }

    pub(crate) fn parse_music_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Music)
    }

    pub(crate) fn parse_bim_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Bim)
    }

    pub(crate) fn parse_city_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::City)
    }

    pub(crate) fn parse_cad_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Cad)
    }

    pub(crate) fn parse_rtl_block(&mut self) -> Result<Node, ParseError> {
        self.parse_domain_block(DomainKind::Rtl)
    }

    // -----------------------------------------------------------------------
    // Core implementation
    // -----------------------------------------------------------------------

    /// Parse a domain block declaration.
    ///
    /// Called after the caller has confirmed the current token is one of the
    /// eight domain keywords. Consumes:
    ///
    /// ```text
    /// <keyword> <Name> `:` NEWLINE INDENT
    ///     (<field_name> `:` <Type> NEWLINE)*
    /// DEDENT
    /// ```
    fn parse_domain_block(&mut self, kind: DomainKind) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume the domain keyword token.
        self.advance();

        // Require a PascalCase (or any) identifier as the block name.
        let name = self.expect_identifier()?;

        // Expect `:` then NEWLINE then INDENT.
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Capture optional inline docstring (first item in the indented body).
        let mut doc_comment: Option<DocComment> = None;
        self.skip_newlines();
        if let TokenKind::String(content) = &self.current.kind {
            doc_comment = Some(DocComment {
                content: content.clone(),
            });
            self.advance();
            self.skip_newlines();
        }

        // Parse fields until DEDENT or EOF.
        let mut fields: Vec<DomainField> = Vec::new();
        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_domain_block")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            fields.push(self.parse_domain_field()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        let span = Span::new(
            start_span.start,
            self.previous.span.end,
            start_span.line,
            start_span.column,
        );

        Ok(Node::DomainBlock(DomainBlockDef {
            span,
            kind,
            name,
            fields,
            attributes: Vec::new(),
            doc_comment,
            visibility: Visibility::Private,
        }))
    }

    /// Dispatch to the correct domain block parser based on the current token.
    ///
    /// Called from `items.rs` when a domain keyword is encountered inside
    /// `pub` or attribute contexts. The current token must be one of the
    /// eight domain keyword variants.
    pub(crate) fn parse_domain_from_kind(&mut self) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Schema => self.parse_schema_block(),
            TokenKind::Style => self.parse_style_block(),
            TokenKind::Ui => self.parse_ui_block(),
            TokenKind::Music => self.parse_music_block(),
            TokenKind::Bim => self.parse_bim_block(),
            TokenKind::City => self.parse_city_block(),
            TokenKind::Cad => self.parse_cad_block(),
            TokenKind::Rtl => self.parse_rtl_block(),
            _ => unreachable!("parse_domain_from_kind called with non-domain token"),
        }
    }

    /// Parse a single domain field: `name: Type NEWLINE`
    fn parse_domain_field(&mut self) -> Result<DomainField, ParseError> {
        let start_span = self.current.span;

        // Optional inline doc comment on the field (leading `/// ...` already
        // handled by the doc-comment scanner; plain string before name is not
        // a field doc — skip for now and keep it simple).
        let name = self.expect_identifier()?;

        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(DomainField {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            ty,
        })
    }
}
