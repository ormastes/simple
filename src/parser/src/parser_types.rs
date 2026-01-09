//! Type parsing methods for Parser
//!
//! This module contains methods for parsing type expressions.

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

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

        // Handle capability prefixes: mut T, iso T
        if self.check(&TokenKind::Mut) {
            self.advance();
            let inner = self.parse_single_type()?;
            return Ok(Type::Capability {
                capability: ReferenceCapability::Exclusive,
                inner: Box::new(inner),
            });
        }
        if self.check_ident("iso") {
            self.advance();
            let inner = self.parse_single_type()?;
            return Ok(Type::Capability {
                capability: ReferenceCapability::Isolated,
                inner: Box::new(inner),
            });
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

        // Handle array type: [T] or [T; N]
        if self.check(&TokenKind::LBracket) {
            self.advance();
            let element = self.parse_type()?;

            // Check for fixed-size array: [T; N]
            let size = if self.check(&TokenKind::Semicolon) {
                self.advance();
                // Parse the size expression
                let size_expr = self.parse_expression()?;
                Some(Box::new(size_expr))
            } else {
                None
            };

            self.expect(&TokenKind::RBracket)?;
            return Ok(Type::Array {
                element: Box::new(element),
                size,
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

        // Handle dynamic trait object: dyn TraitName
        if self.check(&TokenKind::Dyn) {
            self.advance();
            let trait_name = self.expect_identifier()?;
            return Ok(Type::DynTrait(trait_name));
        }

        // Simple or generic type (possibly qualified: module.Type)
        let mut name = self.expect_identifier()?;

        // Check for qualified type name: module.Type or module.submodule.Type
        while self.check(&TokenKind::Dot) {
            self.advance(); // consume '.'
            let segment = self.expect_identifier()?;
            name.push('.');
            name.push_str(&segment);
        }

        // Check for generic arguments - support both [] and <> syntax
        let using_angle_brackets = self.check(&TokenKind::Lt);
        let using_square_brackets = self.check(&TokenKind::LBracket);

        if using_angle_brackets || using_square_brackets {
            self.advance(); // consume '[' or '<'
            let mut args = Vec::new();
            let closing_token = if using_angle_brackets {
                TokenKind::Gt
            } else {
                TokenKind::RBracket
            };

            while !self.check(&closing_token) {
                args.push(self.parse_type()?);
                if !self.check(&closing_token) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&closing_token)?;

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

        // Check for unit type with repr: `_cm:u12` or `_cm where ...`
        // Only for unit types (identifiers starting with underscore)
        if name.starts_with('_') {
            // Check for compact repr syntax: `_cm:u12`
            // The lexer produces Symbol("u12") for `:u12` so we need to check for Symbol
            if let TokenKind::Symbol(repr_str) = &self.current.kind {
                let repr_str = repr_str.clone();
                if let Some(repr) = ReprType::from_str(&repr_str) {
                    self.advance(); // consume the symbol

                    // Check for where clause
                    let constraints = if self.check(&TokenKind::Where) {
                        self.parse_unit_where_clause()?
                    } else {
                        UnitReprConstraints::default()
                    };

                    return Ok(Type::UnitWithRepr {
                        name,
                        repr: Some(repr),
                        constraints,
                    });
                }
            }

            // Check for where clause without repr: `_cm where range: 0..100`
            if self.check(&TokenKind::Where) {
                let constraints = self.parse_unit_where_clause()?;
                return Ok(Type::UnitWithRepr {
                    name,
                    repr: None,
                    constraints,
                });
            }
        }

        Ok(Type::Simple(name))
    }

    /// Parse a repr type in type context (returns ReprType)
    fn parse_repr_type_optional(&mut self) -> Result<ReprType, ParseError> {
        match &self.current.kind {
            TokenKind::Identifier(s) => {
                let s = s.clone();
                if let Some(repr) = ReprType::from_str(&s) {
                    self.advance();
                    Ok(repr)
                } else {
                    Err(ParseError::syntax_error_with_span(
                        format!(
                            "Invalid repr type '{}'. Expected format: u8, i12, f32, etc.",
                            s
                        ),
                        self.current.span,
                    ))
                }
            }
            _ => Err(ParseError::syntax_error_with_span(
                format!(
                    "Expected repr type (u8, i12, f32, etc.), got {:?}",
                    self.current.kind
                ),
                self.current.span,
            )),
        }
    }

    /// Parse where clause for unit types: `where range: 0..100, checked`
    fn parse_unit_where_clause(&mut self) -> Result<UnitReprConstraints, ParseError> {
        self.expect(&TokenKind::Where)?;

        let mut constraints = UnitReprConstraints::default();

        // Parse first constraint
        self.parse_unit_constraint(&mut constraints)?;

        // Parse additional constraints separated by commas
        while self.check(&TokenKind::Comma) {
            self.advance();
            self.parse_unit_constraint(&mut constraints)?;
        }

        Ok(constraints)
    }

    /// Parse a single unit constraint: range, checked, saturate, wrap, default
    fn parse_unit_constraint(
        &mut self,
        constraints: &mut UnitReprConstraints,
    ) -> Result<(), ParseError> {
        match &self.current.kind {
            TokenKind::Identifier(s) => {
                let s = s.clone();
                match s.as_str() {
                    "range" => {
                        self.advance();
                        self.expect(&TokenKind::Colon)?;
                        let (start, end) = self.parse_range_constraint()?;
                        constraints.range = Some((start, end));
                    }
                    "checked" => {
                        self.advance();
                        constraints.overflow = OverflowBehavior::Checked;
                    }
                    "saturate" => {
                        self.advance();
                        constraints.overflow = OverflowBehavior::Saturate;
                    }
                    "wrap" => {
                        self.advance();
                        constraints.overflow = OverflowBehavior::Wrap;
                    }
                    "default" => {
                        self.advance();
                        self.expect(&TokenKind::Colon)?;
                        let expr = self.parse_expression()?;
                        constraints.default_value = Some(Box::new(expr));
                    }
                    _ => {
                        return Err(ParseError::syntax_error_with_span(
                            format!(
                                "Unknown unit constraint '{}'. Expected: range, checked, saturate, wrap, default",
                                s
                            ),
                            self.current.span,
                        ));
                    }
                }
            }
            _ => {
                return Err(ParseError::syntax_error_with_span(
                    format!(
                        "Expected unit constraint (range, checked, saturate, wrap, default), got {:?}",
                        self.current.kind
                    ),
                    self.current.span,
                ));
            }
        }
        Ok(())
    }

    /// Parse range constraint: 0..100 or -500..500
    fn parse_range_constraint(&mut self) -> Result<(i64, i64), ParseError> {
        // Parse start value (can be negative)
        let start = self.parse_integer_literal()?;

        // Expect ..
        self.expect(&TokenKind::DoubleDot)?;

        // Parse end value (can be negative)
        let end = self.parse_integer_literal()?;

        Ok((start, end))
    }

    /// Parse an integer literal (possibly negative)
    fn parse_integer_literal(&mut self) -> Result<i64, ParseError> {
        let negative = if self.check(&TokenKind::Minus) {
            self.advance();
            true
        } else {
            false
        };

        match &self.current.kind {
            TokenKind::Integer(n) => {
                let val = *n;
                self.advance();
                Ok(if negative { -val } else { val })
            }
            _ => Err(ParseError::syntax_error_with_span(
                format!("Expected integer, got {:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
