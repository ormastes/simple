//! Bitfield definition parsing
//!
//! Parses:
//! - `bitfield Name(BackingType): field: width, ...`
//! - `bitfield Name: field: width, ...` (inferred backing type)
//!
//! Example:
//! ```simple
//! bitfield StatusRegister(u32):
//!     carry: 1
//!     zero: 1
//!     overflow: 1
//!     _reserved: 5
//!     mode: 8
//!     const RESET = StatusRegister(carry: 0, zero: 1)
//! ```

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::super::Parser;

impl<'a> Parser<'a> {
    /// Parse a bitfield definition
    pub(crate) fn parse_bitfield(&mut self) -> Result<Node, ParseError> {
        self.parse_bitfield_with_attrs(vec![], None)
    }

    pub(crate) fn parse_bitfield_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Bitfield)?;

        let name = self.expect_identifier()?;

        // Optional base type: bitfield Name(u32):
        let base_type = if self.check(&TokenKind::LParen) {
            self.advance();
            let ty = self.parse_type()?;
            self.expect(&TokenKind::RParen)?;
            Some(ty)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;

        // Parse body (indented block with fields and constants)
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut fields = Vec::new();
        let mut constants = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            // Check for const declaration: const NAME = Value
            if self.check(&TokenKind::Const) {
                self.advance();
                let const_name = self.expect_identifier()?;
                self.expect(&TokenKind::Assign)?;
                let const_value = self.parse_expression()?;
                constants.push(BitfieldConstant {
                    span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                    name: const_name,
                    value: const_value,
                });
            } else {
                // Parse field: name: width or _reserved: width
                let field_span = self.current.span;
                let field_name = if self.check(&TokenKind::Underscore) {
                    self.advance();
                    // Check if followed by identifier for _reserved pattern
                    if let TokenKind::Identifier { name: suffix, .. } = &self.current.kind {
                        let full_name = format!("_{}", suffix);
                        self.advance();
                        full_name
                    } else {
                        "_".to_string()
                    }
                } else {
                    self.expect_identifier()?
                };

                self.expect(&TokenKind::Colon)?;

                // Parse bit width (integer literal)
                let bits = match &self.current.kind {
                    TokenKind::Integer(n) => {
                        let n = *n as u8;
                        self.advance();
                        n
                    }
                    _ => {
                        return Err(ParseError::unexpected_token(
                            "integer (bit width)",
                            format!("{:?}", self.current.kind),
                            self.current.span,
                        ));
                    }
                };

                let is_reserved = field_name.starts_with('_');

                fields.push(BitfieldField {
                    span: field_span,
                    name: field_name,
                    bits,
                    unit_type: None,
                    is_reserved,
                });
            }

            // Consume newline after field/constant
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Bitfield(BitfieldDef {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            name,
            base_type,
            fields,
            constants,
            visibility: Visibility::Private,
            attributes,
            doc_comment,
        }))
    }
}
