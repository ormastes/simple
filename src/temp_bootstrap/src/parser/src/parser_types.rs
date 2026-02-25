//! Type parsing methods for Parser
//!
//! This module contains methods for parsing type expressions.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, Token, TokenKind};

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
        // Handle variadic type: ..T or ...T (e.g., args: ..any, items: ...T)
        if self.check(&TokenKind::DoubleDot) || self.check(&TokenKind::Ellipsis) {
            self.advance();
            let inner = self.parse_single_type()?;
            // Represent variadic as Array of the inner type
            return Ok(Type::Array {
                element: Box::new(inner),
                size: None,
            });
        }

        // Handle function type: fn(T) -> U or bare fn
        if self.check(&TokenKind::Fn) {
            self.advance();
            // Bare `fn` without parens (e.g., `kernel_fn: fn,`)
            if !self.check(&TokenKind::LParen) {
                let ty = Type::Function { params: vec![], ret: None };
                if self.check(&TokenKind::Question) {
                    self.advance();
                    return Ok(Type::Optional(Box::new(ty)));
                }
                return Ok(ty);
            }
            let params = self.parse_paren_type_list()?;
            let ret = if self.check(&TokenKind::Arrow) {
                self.advance();
                Some(Box::new(self.parse_type()?))
            } else {
                None
            };
            let ty = Type::Function { params, ret };
            // Check for optional: fn(T) -> U?  (note: ? applies to whole fn type)
            if self.check(&TokenKind::Question) {
                self.advance();
                return Ok(Type::Optional(Box::new(ty)));
            }
            return Ok(ty);
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
            // Handle mut T, const T, iso T, shared T as type qualifiers
            TokenKind::Mut | TokenKind::Shared | TokenKind::Const => {
                let qualifier = match &self.current.kind {
                    TokenKind::Mut => "mut",
                    TokenKind::Shared => "shared",
                    TokenKind::Const => "const",
                    _ => unreachable!(),
                };
                self.advance();
                let inner = self.parse_single_type()?;
                // Wrap as a simple qualified type: "mut T" -> Type::Simple("mut T") approximately
                // For now, just return the inner type (the qualifier is informational)
                let _ = qualifier;
                return Ok(inner);
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

            let ty = Type::Tuple(types);
            // Check for optional: (T, U)?
            if self.check(&TokenKind::Question) {
                self.advance();
                return Ok(Type::Optional(Box::new(ty)));
            }
            return Ok(ty);
        }

        // Handle array type: [T] or [T; N] or [] (untyped dynamic array)
        if self.check(&TokenKind::LBracket) {
            self.advance();
            // Handle empty array type: [] (dynamic untyped array)
            if self.check(&TokenKind::RBracket) {
                self.advance();
                let ty = Type::Array {
                    element: Box::new(Type::Simple("Any".to_string())),
                    size: None,
                };
                if self.check(&TokenKind::Question) {
                    self.advance();
                    return Ok(Type::Optional(Box::new(ty)));
                }
                return Ok(ty);
            }
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
            let ty = Type::Array {
                element: Box::new(element),
                size,
            };
            // Check for optional: [T]?
            if self.check(&TokenKind::Question) {
                self.advance();
                return Ok(Type::Optional(Box::new(ty)));
            }
            return Ok(ty);
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
                    return Err(ParseError::unexpected_token(
                        "lane count (2, 4, 8, or 16)",
                        format!("{:?}", self.current.kind),
                        self.current.span.clone(),
                    ));
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

        // Handle dict type: {K: V} or set type: {T}
        if self.check(&TokenKind::LBrace) {
            self.advance();
            if self.check(&TokenKind::RBrace) {
                // Empty dict/set type: {} — treat as Dict<Any, Any>
                self.advance();
                return Ok(Type::Dict {
                    key: Box::new(Type::Simple("Any".to_string())),
                    value: Box::new(Type::Simple("Any".to_string())),
                });
            }
            let first_type = self.parse_type()?;
            if self.check(&TokenKind::Colon) {
                // Dict type: {K: V}
                self.advance();
                let value = self.parse_type()?;
                self.expect(&TokenKind::RBrace)?;
                let ty = Type::Dict {
                    key: Box::new(first_type),
                    value: Box::new(value),
                };
                if self.check(&TokenKind::Question) {
                    self.advance();
                    return Ok(Type::Optional(Box::new(ty)));
                }
                return Ok(ty);
            } else {
                // Set type: {T} — represent as Generic Set<T>
                self.expect(&TokenKind::RBrace)?;
                let ty = Type::Generic {
                    name: "Set".to_string(),
                    args: vec![first_type],
                };
                if self.check(&TokenKind::Question) {
                    self.advance();
                    return Ok(Type::Optional(Box::new(ty)));
                }
                return Ok(ty);
            }
        }

        // Handle dynamic trait object: dyn TraitName
        if self.check(&TokenKind::Dyn) {
            self.advance();
            let trait_name = self.expect_identifier()?;
            return Ok(Type::DynTrait(trait_name));
        }

        // Handle nil as a type (void/unit return type)
        if self.check(&TokenKind::Nil) {
            self.advance();
            return Ok(Type::Simple("nil".to_string()));
        }

        // Handle Self type
        if self.check(&TokenKind::Self_) {
            self.advance();
            return Ok(Type::Simple("Self".to_string()));
        }

        // Simple or generic type (may be dot-qualified: module.Type)
        let mut name = self.expect_identifier()?;

        // Handle Fn(...) -> T as function type (capital Fn, like Rust)
        if name == "Fn" && self.check(&TokenKind::LParen) {
            let params = self.parse_paren_type_list()?;
            let ret = if self.check(&TokenKind::Arrow) {
                self.advance();
                Some(Box::new(self.parse_type()?))
            } else {
                None
            };
            let ty = Type::Function { params, ret };
            if self.check(&TokenKind::Question) {
                self.advance();
                return Ok(Type::Optional(Box::new(ty)));
            }
            return Ok(ty);
        }

        // Handle type qualifiers like `iso T`, `owned T`, `const T` where a type follows
        if matches!(name.as_str(), "iso" | "owned" | "unique" | "ref" | "pin" | "lazy") {
            // If followed by a type-starting token, parse the inner type
            if matches!(&self.current.kind,
                TokenKind::Identifier(_) | TokenKind::Self_ | TokenKind::Dyn
                | TokenKind::LParen | TokenKind::LBracket | TokenKind::Fn
                | TokenKind::Ampersand | TokenKind::Star
            ) {
                let _inner = self.parse_single_type()?;
                return Ok(_inner); // drop qualifier for now, keep inner type
            }
        }

        // Handle dot-qualified type names: protocol.SourceBreakpoint, std.Option
        while self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) {
            self.advance();
            let segment = self.expect_identifier()?;
            name = format!("{}.{}", name, segment);
        }

        // Check for generic arguments: Name[T, U] or Name<T, U>
        if self.check(&TokenKind::LBracket) || self.check(&TokenKind::Lt) {
            let (open_is_angle, close_token) = if self.check(&TokenKind::Lt) {
                (true, TokenKind::Gt)
            } else {
                (false, TokenKind::RBracket)
            };
            self.advance();
            let mut args = Vec::new();
            // Skip whitespace after opening delimiter (for multi-line generic args)
            self.skip_whitespace_tokens();
            while !self.check(&close_token)
                && !(open_is_angle && self.check(&TokenKind::ShiftRight))
            {
                // Handle const generic argument: const N: usize
                if self.check(&TokenKind::Const) {
                    self.advance(); // consume 'const'
                    let _name = self.expect_identifier()?; // consume parameter name
                    // Skip optional type annotation: `: usize`
                    if self.check(&TokenKind::Colon) {
                        self.advance();
                        let ty = self.parse_type()?;
                        args.push(ty);
                    } else {
                        args.push(Type::Simple("const".to_string()));
                    }
                } else if matches!(&self.current.kind, TokenKind::Integer(_) | TokenKind::TypedInteger(_, _)) {
                    // Integer literal as const generic value: Array[T, 2]
                    let val = match &self.current.kind {
                        TokenKind::Integer(n) => n.to_string(),
                        TokenKind::TypedInteger(n, _) => n.to_string(),
                        _ => unreachable!(),
                    };
                    self.advance();
                    args.push(Type::Simple(val));
                } else {
                    let ty = self.parse_type()?;
                    // Handle associated type binding: Item=T or Item: T inside generic args
                    if self.check(&TokenKind::Assign) {
                        // Associated type binding: Name=Type  (e.g., Iterator[Item=T])
                        self.advance(); // consume '='
                        let bound_ty = self.parse_type()?;
                        args.push(bound_ty);
                    } else {
                        args.push(ty);
                    }
                }
                // Skip whitespace after type argument
                self.skip_whitespace_tokens();
                if !self.check(&close_token)
                    && !(open_is_angle && self.check(&TokenKind::ShiftRight))
                {
                    if self.check(&TokenKind::Comma) {
                        self.advance();
                    } else {
                        self.expect(&TokenKind::Comma)?;
                    }
                    // Skip whitespace after comma
                    self.skip_whitespace_tokens();
                }
            }
            // Handle >> as two > tokens for nested generics like Dict<text, List<text>>
            if open_is_angle && self.check(&TokenKind::ShiftRight) {
                // Split >> into > + >.
                // The first > closes the inner generic (this one).
                // The second > becomes the current token so the outer generic can consume it.
                let span = self.current.span;
                // Replace current >> with a synthetic > (the second >)
                // and save whatever was going to be the next token
                let next_token = self.pending_token
                    .take()
                    .unwrap_or_else(|| self.lexer.next_token());
                self.pending_token = Some(next_token);
                self.current = Token::new(
                    TokenKind::Gt,
                    Span::new(span.start + 1, span.end, span.line, span.column + 1),
                    ">".to_string(),
                );
            } else {
                self.expect(&close_token)?;
            }

            // Special handling for Constructor[T] or Constructor<T, (args)>
            if name == "Constructor" {
                if args.is_empty() {
                    return Err(ParseError::unexpected_token(
                        "type parameter for Constructor",
                        format!("{:?}", self.current.kind),
                        self.current.span.clone(),
                    ));
                }
                let target = Box::new(args.remove(0));
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

            let mut ty = Type::Generic { name, args };
            // Check for optional after generic: Result<T, E>?, Result<T, E>??, etc.
            loop {
                if self.check(&TokenKind::DoubleQuestion) {
                    self.advance();
                    ty = Type::Optional(Box::new(Type::Optional(Box::new(ty))));
                } else if self.check(&TokenKind::Question) {
                    self.advance();
                    ty = Type::Optional(Box::new(ty));
                } else {
                    break;
                }
            }
            return Ok(ty);
        }

        // Check for optional: Name?, Name??, Name???, etc.
        let mut ty = Type::Simple(name);
        loop {
            if self.check(&TokenKind::DoubleQuestion) {
                self.advance();
                ty = Type::Optional(Box::new(Type::Optional(Box::new(ty))));
            } else if self.check(&TokenKind::Question) {
                self.advance();
                ty = Type::Optional(Box::new(ty));
            } else {
                break;
            }
        }
        Ok(ty)
    }

    /// Parse a type for cast expressions (`as Type`).
    /// Does NOT consume trailing `?` or `??` as optional suffixes,
    /// since in `expr as Type ?? default`, `??` is the null-coalesce operator.
    pub(crate) fn parse_type_for_cast(&mut self) -> Result<Type, ParseError> {
        // Parse the base type
        let ty = self.parse_type()?;
        // If the type parser consumed ?? or ? (making it Optional), push back
        // the operator token. In cast context, `as i64 ?? default` means
        // `(as i64) ?? default`, not `as (i64??)`.
        match &ty {
            Type::Optional(inner) => {
                match inner.as_ref() {
                    Type::Optional(innermost) => {
                        // Double optional from ?? consumption — push back ??
                        // Save current token, replace self.current with ??
                        let saved_current = self.current.clone();
                        if let Some(pending) = self.pending_token.take() {
                            self.lexer.pending_tokens.push(saved_current);
                            self.lexer.pending_tokens.push(pending);
                        } else {
                            self.lexer.pending_tokens.push(saved_current);
                        }
                        self.current = Token {
                            kind: TokenKind::DoubleQuestion,
                            span: self.previous.span,
                            lexeme: "??".to_string(),
                        };
                        // Unwrap both levels: Optional(Optional(Simple(x))) -> Simple(x)
                        Ok(*innermost.clone())
                    }
                    _ => {
                        // Single optional from ? consumption — push back ?
                        let saved_current = self.current.clone();
                        if let Some(pending) = self.pending_token.take() {
                            self.lexer.pending_tokens.push(saved_current);
                            self.lexer.pending_tokens.push(pending);
                        } else {
                            self.lexer.pending_tokens.push(saved_current);
                        }
                        self.current = Token {
                            kind: TokenKind::Question,
                            span: self.previous.span,
                            lexeme: "?".to_string(),
                        };
                        Ok(*inner.clone())
                    }
                }
            }
            _ => Ok(ty),
        }
    }
}
