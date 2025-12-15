//! Type parsing methods for Parser
//!
//! This module contains methods for parsing type expressions.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::TokenKind;

use super::Parser;

impl<'a> Parser<'a> {
    // === Type Parsing ===

    pub(crate) fn parse_type(&mut self) -> Result<Type, ParseError> {
        // Parse the first type
        let first = self.parse_single_type()?;

        // Check for union types (A | B | C)
        if self.check(&TokenKind::Pipe) {
            let mut types = vec![first];
            while self.check(&TokenKind::Pipe) {
                self.advance();
                types.push(self.parse_single_type()?);
            }
            return Ok(Type::Union(types));
        }

        Ok(first)
    }

    pub(crate) fn parse_single_type(&mut self) -> Result<Type, ParseError> {
        // Handle function type: fn(T) -> U
        if self.check(&TokenKind::Fn) {
            self.advance();
            let params = self.parse_paren_type_list()?;
            let ret = if self.check(&TokenKind::Arrow) {
                self.advance();
                Some(Box::new(self.parse_type()?))
            } else {
                None
            };
            return Ok(Type::Function { params, ret });
        }

        // Handle pointer types
        match &self.current.kind {
            TokenKind::Ampersand => {
                self.advance();
                // Check for &mut T (mutable borrow)
                if self.check(&TokenKind::Mut) {
                    self.advance();
                    let inner = self.parse_single_type()?;
                    return Ok(Type::Pointer {
                        kind: PointerKind::BorrowMut,
                        inner: Box::new(inner),
                    });
                }
                // Parse the inner type
                let inner = self.parse_single_type()?;
                // Check if it's a borrow type (ends with _borrow suffix in the type name)
                // or explicit borrow via &T_borrow
                let kind = if self.is_borrow_type(&inner) {
                    PointerKind::Borrow
                } else {
                    PointerKind::Unique
                };
                return Ok(Type::Pointer {
                    kind,
                    inner: Box::new(inner),
                });
            }
            TokenKind::Star => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer {
                    kind: PointerKind::Shared,
                    inner: Box::new(inner),
                });
            }
            TokenKind::Minus => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer {
                    kind: PointerKind::Weak,
                    inner: Box::new(inner),
                });
            }
            TokenKind::Plus => {
                self.advance();
                let inner = self.parse_single_type()?;
                return Ok(Type::Pointer {
                    kind: PointerKind::Handle,
                    inner: Box::new(inner),
                });
            }
            _ => {}
        }

        // Handle tuple type
        if self.check(&TokenKind::LParen) {
            let types = self.parse_paren_type_list()?;

            // Check if it's a function type
            if self.check(&TokenKind::Arrow) {
                self.advance();
                let ret = self.parse_type()?;
                return Ok(Type::Function {
                    params: types,
                    ret: Some(Box::new(ret)),
                });
            }

            return Ok(Type::Tuple(types));
        }

        // Handle array type
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let element = self.parse_type()?;
            self.expect(&TokenKind::RBracket)?;
            return Ok(Type::Array {
                element: Box::new(element),
                size: None,
            });
        }

        // Handle SIMD vector type: vec[N, T]
        if self.check(&TokenKind::Vec) {
            self.advance();
            self.expect(&TokenKind::LBracket)?;

            // Parse lane count (must be an integer literal)
            let lanes = match &self.current.kind {
                TokenKind::Integer(n) => {
                    let lanes = *n as u32;
                    self.advance();
                    lanes
                }
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        expected: "lane count (2, 4, 8, or 16)".to_string(),
                        found: format!("{:?}", self.current.kind),
                        span: self.current.span.clone(),
                    });
                }
            };

            self.expect(&TokenKind::Comma)?;
            let element = self.parse_type()?;
            self.expect(&TokenKind::RBracket)?;

            return Ok(Type::Simd {
                lanes,
                element: Box::new(element),
            });
        }

        // Simple or generic type
        let name = self.expect_identifier()?;

        // Check for generic arguments
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RBracket) {
                args.push(self.parse_type()?);
                if !self.check(&TokenKind::RBracket) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RBracket)?;

            // Special handling for Constructor[T] or Constructor[T, (args)]
            if name == "Constructor" {
                if args.is_empty() {
                    return Err(ParseError::UnexpectedToken {
                        expected: "type parameter for Constructor".to_string(),
                        found: format!("{:?}", self.current.kind),
                        span: self.current.span.clone(),
                    });
                }
                let target = Box::new(args.remove(0));
                // If there's a second arg, it should be a tuple of argument types
                let ctor_args = if args.is_empty() {
                    None
                } else if args.len() == 1 {
                    match args.remove(0) {
                        Type::Tuple(types) => Some(types),
                        single_type => Some(vec![single_type]),
                    }
                } else {
                    Some(args)
                };
                return Ok(Type::Constructor {
                    target,
                    args: ctor_args,
                });
            }

            return Ok(Type::Generic { name, args });
        }

        // Check for optional
        if self.check(&TokenKind::Question) {
            self.advance();
            return Ok(Type::Optional(Box::new(Type::Simple(name))));
        }

        Ok(Type::Simple(name))
    }
}
