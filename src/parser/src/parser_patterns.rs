//! Pattern parsing methods for Parser
//!
//! This module contains methods for parsing pattern expressions used in match statements.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::TokenKind;

use super::Parser;

impl<'a> Parser<'a> {
    // === Pattern Parsing ===

    pub(crate) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        // Parse the first pattern
        let first = self.parse_single_pattern()?;

        // Check for or patterns (pattern1 | pattern2 | ...)
        if self.check(&TokenKind::Pipe) {
            let mut patterns = vec![first];
            while self.check(&TokenKind::Pipe) {
                self.advance();
                patterns.push(self.parse_single_pattern()?);
            }
            return Ok(Pattern::Or(patterns));
        }

        Ok(first)
    }

    fn parse_single_pattern(&mut self) -> Result<Pattern, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            TokenKind::Mut => {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(Pattern::MutIdentifier(name))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();

                // Check for struct pattern: Name { ... }
                if self.check(&TokenKind::LBrace) {
                    self.advance();
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        let pattern = if self.check(&TokenKind::Colon) {
                            self.advance();
                            self.parse_pattern()?
                        } else {
                            Pattern::Identifier(field_name.clone())
                        };
                        fields.push((field_name, pattern));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Pattern::Struct { name, fields });
                }

                // Check for enum variant: Name::Variant or Name::Variant(...)
                // Also supports dot syntax: Name.Variant or Name.Variant(...)
                if self.check(&TokenKind::DoubleColon) || self.check(&TokenKind::Dot) {
                    self.advance();
                    let variant = self.expect_identifier()?;
                    let payload = if self.check(&TokenKind::LParen) {
                        self.advance();
                        let mut patterns = Vec::new();
                        while !self.check(&TokenKind::RParen) {
                            patterns.push(self.parse_pattern()?);
                            if !self.check(&TokenKind::RParen) {
                                self.expect(&TokenKind::Comma)?;
                            }
                        }
                        self.expect(&TokenKind::RParen)?;
                        Some(patterns)
                    } else {
                        None
                    };
                    return Ok(Pattern::Enum {
                        name,
                        variant,
                        payload,
                    });
                }

                // Check for unit enum variants without parentheses: None
                // These are builtin variants that don't take a payload
                if name == "None" {
                    return Ok(Pattern::Enum {
                        name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: None,
                    });
                }

                // Check for enum variant pattern with parentheses: VariantName(...)
                // This handles both builtin (Some, Ok, Err) and user-defined variants
                if self.check(&TokenKind::LParen) {
                    // Map builtin variants to their enum types
                    let (enum_name, variant) = match name.as_str() {
                        "Some" => ("Option".to_string(), "Some".to_string()),
                        "Ok" => ("Result".to_string(), "Ok".to_string()),
                        "Err" => ("Result".to_string(), "Err".to_string()),
                        // For user-defined variants, use "_" as placeholder enum name
                        // The interpreter will resolve based on the value being matched
                        _ => ("_".to_string(), name.clone()),
                    };
                    self.advance(); // consume LParen
                    let mut patterns = Vec::new();
                    while !self.check(&TokenKind::RParen) {
                        patterns.push(self.parse_pattern()?);
                        if !self.check(&TokenKind::RParen) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Pattern::Enum {
                        name: enum_name,
                        variant,
                        payload: Some(patterns),
                    });
                }

                // Check for typed pattern: name: Type (for union type discrimination)
                // This must be distinguished from struct field patterns, which are only
                // valid inside struct patterns (handled above in LBrace case)
                if self.check(&TokenKind::Colon) {
                    self.advance();
                    let ty = self.parse_type()?;
                    return Ok(Pattern::Typed {
                        pattern: Box::new(Pattern::Identifier(name)),
                        ty,
                    });
                }

                Ok(Pattern::Identifier(name))
            }
            TokenKind::Integer(_)
            | TokenKind::TypedInteger(_, _)
            | TokenKind::Float(_)
            | TokenKind::TypedFloat(_, _)
            | TokenKind::String(_)
            | TokenKind::RawString(_)
            | TokenKind::FString(_)
            | TokenKind::Bool(_)
            | TokenKind::Nil => {
                let expr = self.parse_primary()?;
                // Check for range pattern: start..end or start..=end
                if self.check(&TokenKind::DoubleDot) {
                    self.advance();
                    let end_expr = self.parse_primary()?;
                    return Ok(Pattern::Range {
                        start: Box::new(expr),
                        end: Box::new(end_expr),
                        inclusive: false,
                    });
                }
                if self.check(&TokenKind::DoubleDotEq) {
                    self.advance();
                    let end_expr = self.parse_primary()?;
                    return Ok(Pattern::Range {
                        start: Box::new(expr),
                        end: Box::new(end_expr),
                        inclusive: true,
                    });
                }
                Ok(Pattern::Literal(Box::new(expr)))
            }
            TokenKind::LParen => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RParen) {
                    patterns.push(self.parse_pattern()?);
                    if !self.check(&TokenKind::RParen) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Pattern::Tuple(patterns))
            }
            TokenKind::LBracket => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RBracket) {
                    if self.check(&TokenKind::Ellipsis) {
                        self.advance();
                        patterns.push(Pattern::Rest);
                    } else {
                        patterns.push(self.parse_pattern()?);
                    }
                    if !self.check(&TokenKind::RBracket) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Pattern::Array(patterns))
            }
            // Allow certain keywords to be used as identifier patterns
            TokenKind::Out => {
                self.advance();
                Ok(Pattern::Identifier("out".to_string()))
            }
            TokenKind::OutErr => {
                self.advance();
                Ok(Pattern::Identifier("out_err".to_string()))
            }
            TokenKind::Type => {
                self.advance();
                Ok(Pattern::Identifier("type".to_string()))
            }
            TokenKind::Result => {
                self.advance();
                Ok(Pattern::Identifier("result".to_string()))
            }
            TokenKind::To => {
                self.advance();
                Ok(Pattern::Identifier("to".to_string()))
            }
            TokenKind::NotTo => {
                self.advance();
                Ok(Pattern::Identifier("not_to".to_string()))
            }
            _ => Err(ParseError::unexpected_token(
                "pattern",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
