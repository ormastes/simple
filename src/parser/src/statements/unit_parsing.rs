//! Unit variant parsing
//!
//! This module handles parsing of unit variants and related numeric operations.

use crate::ast::UnitVariant;
use crate::error::ParseError;
use crate::token::TokenKind;
use crate::Parser;

impl<'a> Parser<'a> {
    /// Helper to parse a number (float or int) as f64.
    pub(super) fn parse_number_as_f64(&mut self) -> Result<f64, ParseError> {
        if let TokenKind::Float(f) = &self.current.kind {
            let val = *f;
            self.advance();
            Ok(val)
        } else if let TokenKind::Integer(i) = &self.current.kind {
            let val = *i as f64;
            self.advance();
            Ok(val)
        } else {
            Err(ParseError::unexpected_token(
                "number",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Helper to parse a unit variant (suffix = factor)
    pub(super) fn parse_unit_variant(&mut self) -> Result<UnitVariant, ParseError> {
        let suffix = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let factor = self.parse_number_as_f64()?;
        Ok(UnitVariant { suffix, factor })
    }
}
