//! Simple language parser
//!
//! This module provides a recursive descent parser with Pratt parsing for expressions.
//! The parser is split into multiple submodules for maintainability:
//! - `expressions/` - Expression parsing (Pratt parser)
//! - `statements/` - Statement parsing (let, if, for, etc.)
//! - `types_def/` - Type definition parsing (struct, class, enum, etc.)

use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::Lexer;
use crate::token::{Span, Token, TokenKind};

pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) current: Token,
    pub(crate) previous: Token,
    #[allow(dead_code)]
    source: &'a str,
    pub(crate) pending_token: Option<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let previous = Token::new(TokenKind::Eof, Span::new(0, 0, 1, 1), String::new());

        Self {
            lexer,
            current,
            previous,
            source,
            pending_token: None,
        }
    }

    pub fn parse(&mut self) -> Result<Module, ParseError> {
        let mut items = Vec::new();

        while !self.is_at_end() {
            // Skip newlines at top level
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }

            items.push(self.parse_item()?);
        }

        Ok(Module { name: None, items })
    }

    pub(crate) fn parse_item(&mut self) -> Result<Node, ParseError> {
        // Skip leading newlines
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        match &self.current.kind {
            TokenKind::Hash => self.parse_attributed_item(),
            TokenKind::At => self.parse_decorated_function(),
            TokenKind::Fn => self.parse_function(),
            TokenKind::Async => self.parse_async_function(),
            TokenKind::Struct => self.parse_struct(),
            TokenKind::Class => self.parse_class(),
            TokenKind::Enum => self.parse_enum(),
            TokenKind::Trait => self.parse_trait(),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Actor => self.parse_actor(),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item()
            }
            TokenKind::Mut => self.parse_mut_let(),
            TokenKind::Let => self.parse_let(),
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => self.parse_static(),
            TokenKind::Type => self.parse_type_alias(),
            TokenKind::Unit => self.parse_unit(),
            TokenKind::Extern => self.parse_extern(),
            TokenKind::Macro => self.parse_macro_def(),
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match_stmt(),
            TokenKind::For => self.parse_for(),
            TokenKind::While => self.parse_while(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => self.parse_break(),
            TokenKind::Continue => self.parse_continue(),
            TokenKind::Context => self.parse_context(),
            TokenKind::With => self.parse_with(),
            _ => self.parse_expression_or_assignment(),
        }
    }

    fn parse_pub_item(&mut self) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Async => {
                let mut node = self.parse_async_function()?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct()?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class()?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Enum => {
                let mut node = self.parse_enum()?;
                if let Node::Enum(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Trait => {
                let mut node = self.parse_trait()?;
                if let Node::Trait(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Actor => {
                let mut node = self.parse_actor()?;
                if let Node::Actor(ref mut a) = node {
                    a.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Const => {
                let mut node = self.parse_const()?;
                if let Node::Const(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Static => {
                let mut node = self.parse_static()?;
                if let Node::Static(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Type => {
                let mut node = self.parse_type_alias()?;
                if let Node::TypeAlias(ref mut t) = node {
                    t.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Unit => {
                let mut node = self.parse_unit()?;
                if let Node::Unit(ref mut u) = node {
                    u.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Extern => {
                let mut node = self.parse_extern()?;
                if let Node::Extern(ref mut e) = node {
                    e.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Macro => {
                let mut node = self.parse_macro_def()?;
                if let Node::Macro(ref mut m) = node {
                    m.visibility = Visibility::Public;
                }
                Ok(node)
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, trait, actor, const, static, type, extern, or macro after 'pub'",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Function Parsing ===

    pub(crate) fn parse_async_function(&mut self) -> Result<Node, ParseError> {
        self.advance(); // consume 'async'
        let mut func = self.parse_function()?;
        if let Node::Function(ref mut f) = func {
            f.effect = Some(Effect::Async);
        }
        Ok(func)
    }

    pub(crate) fn parse_function(&mut self) -> Result<Node, ParseError> {
        self.parse_function_with_decorators(vec![])
    }

    fn parse_function_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Function(FunctionDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            params,
            return_type,
            body,
            visibility: Visibility::Private,
            effect: None,
            decorators,
            attributes: vec![],
        }))
    }

    fn parse_function_with_attrs(
        &mut self,
        decorators: Vec<Decorator>,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Function(FunctionDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params,
            params,
            return_type,
            body,
            visibility: Visibility::Private,
            effect: None,
            decorators,
            attributes,
        }))
    }

    /// Parse an attributed item: #[attr] fn/struct/class/etc
    fn parse_attributed_item(&mut self) -> Result<Node, ParseError> {
        let mut attributes = Vec::new();

        // Parse all attributes (can be multiple: #[a] #[b] fn foo)
        while self.check(&TokenKind::Hash) {
            attributes.push(self.parse_attribute()?);
            // Skip newlines between attributes
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the item with collected attributes
        // Could be function, struct, class, etc.
        match &self.current.kind {
            TokenKind::At => {
                // Attributes followed by decorators
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    decorators.push(self.parse_decorator()?);
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }
                self.parse_function_with_attrs(decorators, attributes)
            }
            TokenKind::Fn => self.parse_function_with_attrs(vec![], attributes),
            TokenKind::Async => {
                self.advance();
                let mut func = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = func {
                    f.effect = Some(Effect::Async);
                }
                Ok(func)
            }
            TokenKind::Struct => self.parse_struct_with_attrs(attributes),
            TokenKind::Class => self.parse_class_with_attrs(attributes),
            TokenKind::Enum => self.parse_enum_with_attrs(attributes),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_attrs(attributes)
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, class, enum, or pub after attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse a single attribute: #[name] or #[name = value] or #[name(args)]
    fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Hash)?;
        self.expect(&TokenKind::LBracket)?;

        // Parse the attribute name
        let name = self.expect_identifier()?;

        // Check for value: #[name = value]
        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // Check for arguments: #[name(arg1, arg2)]
        let args = if self.check(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) {
                args.push(self.parse_expression()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Some(args)
        } else {
            None
        };

        self.expect(&TokenKind::RBracket)?;

        Ok(Attribute {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            value,
            args,
        })
    }

    fn parse_pub_item_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        match &self.current.kind {
            TokenKind::Fn => {
                let mut node = self.parse_function_with_attrs(vec![], attributes)?;
                if let Node::Function(ref mut f) = node {
                    f.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Struct => {
                let mut node = self.parse_struct_with_attrs(attributes)?;
                if let Node::Struct(ref mut s) = node {
                    s.visibility = Visibility::Public;
                }
                Ok(node)
            }
            TokenKind::Class => {
                let mut node = self.parse_class_with_attrs(attributes)?;
                if let Node::Class(ref mut c) = node {
                    c.visibility = Visibility::Public;
                }
                Ok(node)
            }
            _ => Err(ParseError::unexpected_token(
                "fn, struct, or class after pub with attributes",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse a decorated function: @decorator fn foo(): ...
    fn parse_decorated_function(&mut self) -> Result<Node, ParseError> {
        let mut decorators = Vec::new();

        // Parse all decorators (can be multiple: @a @b fn foo)
        while self.check(&TokenKind::At) {
            decorators.push(self.parse_decorator()?);
            // Skip newlines between decorators
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Now parse the function with the collected decorators
        self.parse_function_with_decorators(decorators)
    }

    /// Parse a single decorator: @name or @name(args)
    fn parse_decorator(&mut self) -> Result<Decorator, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Parse the decorator name (can be dotted: @module.decorator)
        let name = self.parse_primary()?;

        // Check for arguments: @decorator(arg1, arg2)
        let args = if self.check(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) {
                args.push(self.parse_expression()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Some(args)
        } else {
            None
        };

        Ok(Decorator {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            args,
        })
    }

    pub(crate) fn parse_parameters(&mut self) -> Result<Vec<Parameter>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();

        while !self.check(&TokenKind::RParen) {
            let param_span = self.current.span;
            let mutability = if self.check(&TokenKind::Mut) {
                self.advance();
                Mutability::Mutable
            } else {
                Mutability::Immutable
            };

            // Allow 'self' as a parameter name for method definitions
            let name = if self.check(&TokenKind::Self_) {
                self.advance();
                "self".to_string()
            } else {
                self.expect_identifier()?
            };

            let ty = if self.check(&TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };

            let default = if self.check(&TokenKind::Assign) {
                self.advance();
                Some(self.parse_expression()?)
            } else {
                None
            };

            params.push(Parameter {
                span: param_span,
                name,
                ty,
                default,
                mutability,
            });

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    pub(crate) fn parse_block(&mut self) -> Result<Block, ParseError> {
        let start_span = self.current.span;

        // Expect NEWLINE then INDENT
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut statements = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            statements.push(self.parse_item()?);

            // Consume newline after statement if present
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Block {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            statements,
        })
    }

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

    fn parse_single_type(&mut self) -> Result<Type, ParseError> {
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
            self.advance();
            let mut types = Vec::new();
            while !self.check(&TokenKind::RParen) {
                types.push(self.parse_type()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;

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
                if self.check(&TokenKind::DoubleColon) {
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

                // Check for builtin enum pattern without qualifier: Some(x), Ok(val), Err(e)
                // These are shorthand for Option::Some, Result::Ok, Result::Err
                if self.check(&TokenKind::LParen) {
                    let (enum_name, variant) = match name.as_str() {
                        "Some" => ("Option".to_string(), "Some".to_string()),
                        "Ok" => ("Result".to_string(), "Ok".to_string()),
                        "Err" => ("Result".to_string(), "Err".to_string()),
                        _ => {
                            // Not a known builtin enum variant, treat as identifier
                            return Ok(Pattern::Identifier(name));
                        }
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
            _ => Err(ParseError::unexpected_token(
                "pattern",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    // === Helper Methods ===

    pub(crate) fn advance(&mut self) {
        self.previous = std::mem::replace(
            &mut self.current,
            self.pending_token
                .take()
                .unwrap_or_else(|| self.lexer.next_token()),
        );
    }

    pub(crate) fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current.kind) == std::mem::discriminant(kind)
    }

    pub(crate) fn is_at_end(&self) -> bool {
        self.current.kind == TokenKind::Eof
    }

    /// Peek at the next token without consuming current
    pub(crate) fn peek_is(&mut self, kind: &TokenKind) -> bool {
        // Save current state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        // Advance to peek
        self.advance();
        let result = self.check(kind);

        // Restore state
        self.pending_token = Some(self.current.clone());
        self.current = saved_current;
        self.previous = saved_previous;

        result
    }

    /// Parse array with spread operators: [*a, 1, *b]
    pub(crate) fn parse_array_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut elements = Vec::new();

        while !self.check(&TokenKind::RBracket) {
            if self.check(&TokenKind::Star) {
                self.advance();
                elements.push(Expr::Spread(Box::new(self.parse_expression()?)));
            } else {
                elements.push(self.parse_expression()?);
            }
            if !self.check(&TokenKind::RBracket) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(Expr::Array(elements))
    }

    /// Parse dict with spread operators: {**d1, "key": value, **d2}
    pub(crate) fn parse_dict_with_spreads(&mut self) -> Result<Expr, ParseError> {
        let mut pairs = Vec::new();

        while !self.check(&TokenKind::RBrace) {
            if self.check(&TokenKind::Star) && self.peek_is(&TokenKind::Star) {
                self.advance(); // first *
                self.advance(); // second *
                let spread_expr = self.parse_expression()?;
                pairs.push((Expr::DictSpread(Box::new(spread_expr)), Expr::Nil));
            } else {
                let key = self.parse_expression()?;
                self.expect(&TokenKind::Colon)?;
                let value = self.parse_expression()?;
                pairs.push((key, value));
            }
            if !self.check(&TokenKind::RBrace) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(Expr::Dict(pairs))
    }

    pub(crate) fn expect(&mut self, kind: &TokenKind) -> Result<(), ParseError> {
        if self.check(kind) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                format!("{:?}", kind),
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    pub(crate) fn expect_identifier(&mut self) -> Result<String, ParseError> {
        if let TokenKind::Identifier(name) = &self.current.kind {
            let name = name.clone();
            self.advance();
            Ok(name)
        } else {
            Err(ParseError::unexpected_token(
                "identifier",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Check if a type should be treated as a borrow type
    /// Types ending with _borrow are borrow references
    fn is_borrow_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Simple(name) => name.ends_with("_borrow"),
            Type::Generic { name, .. } => name.ends_with("_borrow"),
            _ => false,
        }
    }

    /// Parse generic type parameters: <T, U, V>
    /// Returns empty Vec if no generic parameters are present
    pub(crate) fn parse_generic_params(&mut self) -> Result<Vec<String>, ParseError> {
        if !self.check(&TokenKind::Lt) {
            return Ok(Vec::new());
        }
        self.advance(); // consume '<'

        let mut params = Vec::new();
        while !self.check(&TokenKind::Gt) {
            let name = self.expect_identifier()?;
            params.push(name);

            if !self.check(&TokenKind::Gt) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::Gt)?; // consume '>'

        Ok(params)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    fn parse(source: &str) -> Result<Module, ParseError> {
        let mut parser = Parser::new(source);
        parser.parse()
    }

    // === Expression Tests ===

    #[test]
    fn test_integer_literal() {
        let module = parse("42").unwrap();
        assert_eq!(module.items.len(), 1);
        if let Node::Expression(Expr::Integer(n)) = &module.items[0] {
            assert_eq!(*n, 42);
        } else {
            panic!("Expected integer expression");
        }
    }

    #[test]
    fn test_binary_expression() {
        let module = parse("1 + 2").unwrap();
        assert_eq!(module.items.len(), 1);
        if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
            assert_eq!(*op, BinOp::Add);
            assert_eq!(**left, Expr::Integer(1));
            assert_eq!(**right, Expr::Integer(2));
        } else {
            panic!("Expected binary expression");
        }
    }

    #[test]
    fn test_operator_precedence() {
        let module = parse("1 + 2 * 3").unwrap();
        // Should parse as 1 + (2 * 3)
        if let Node::Expression(Expr::Binary { op, left, right }) = &module.items[0] {
            assert_eq!(*op, BinOp::Add);
            assert_eq!(**left, Expr::Integer(1));
            if let Expr::Binary { op: inner_op, .. } = &**right {
                assert_eq!(*inner_op, BinOp::Mul);
            } else {
                panic!("Expected nested binary");
            }
        } else {
            panic!("Expected binary expression");
        }
    }

    #[test]
    fn test_function_call() {
        let module = parse("foo(1, 2)").unwrap();
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            assert_eq!(**callee, Expr::Identifier("foo".to_string()));
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected call expression");
        }
    }

    #[test]
    fn test_method_call() {
        let module = parse("obj.method(x)").unwrap();
        if let Node::Expression(Expr::MethodCall {
            receiver,
            method,
            args,
        }) = &module.items[0]
        {
            assert_eq!(**receiver, Expr::Identifier("obj".to_string()));
            assert_eq!(method, "method");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected method call");
        }
    }

    #[test]
    fn test_array_literal() {
        let module = parse("[1, 2, 3]").unwrap();
        if let Node::Expression(Expr::Array(elements)) = &module.items[0] {
            assert_eq!(elements.len(), 3);
        } else {
            panic!("Expected array literal");
        }
    }

    // === Statement Tests ===

    #[test]
    fn test_let_statement() {
        let module = parse("let x = 42").unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            assert_eq!(stmt.mutability, Mutability::Immutable);
            if let Pattern::Identifier(name) = &stmt.pattern {
                assert_eq!(name, "x");
            }
        } else {
            panic!("Expected let statement");
        }
    }

    #[test]
    fn test_let_mut_statement() {
        let module = parse("let mut x = 42").unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            assert_eq!(stmt.mutability, Mutability::Mutable);
        } else {
            panic!("Expected let statement");
        }
    }

    // === Function Tests ===

    #[test]
    fn test_function_definition() {
        let source = "fn add(a: i64, b: i64) -> i64:\n    return a + b";
        let module = parse(source).unwrap();
        if let Node::Function(func) = &module.items[0] {
            assert_eq!(func.name, "add");
            assert_eq!(func.params.len(), 2);
            assert!(func.return_type.is_some());
        } else {
            panic!("Expected function definition");
        }
    }

    #[test]
    fn test_simple_function() {
        let source = "fn greet():\n    print(\"hello\")";
        let module = parse(source).unwrap();
        if let Node::Function(func) = &module.items[0] {
            assert_eq!(func.name, "greet");
            assert_eq!(func.params.len(), 0);
        } else {
            panic!("Expected function definition");
        }
    }

    // === Struct Tests ===

    #[test]
    fn test_struct_definition() {
        let source = "struct Point:\n    x: f64\n    y: f64";
        let module = parse(source).unwrap();
        if let Node::Struct(s) = &module.items[0] {
            assert_eq!(s.name, "Point");
            assert_eq!(s.fields.len(), 2);
        } else {
            panic!("Expected struct definition");
        }
    }

    // === Enum Tests ===

    #[test]
    fn test_enum_definition() {
        let source = "enum Option:\n    Some(i64)\n    None";
        let module = parse(source).unwrap();
        if let Node::Enum(e) = &module.items[0] {
            assert_eq!(e.name, "Option");
            assert_eq!(e.variants.len(), 2);
        } else {
            panic!("Expected enum definition");
        }
    }

    // === Control Flow Tests ===

    #[test]
    fn test_if_statement() {
        let source = "if x > 0:\n    print(x)";
        let module = parse(source).unwrap();
        if let Node::If(stmt) = &module.items[0] {
            assert!(stmt.else_block.is_none());
            assert!(stmt.elif_branches.is_empty());
        } else {
            panic!("Expected if statement");
        }
    }

    #[test]
    fn test_for_loop() {
        let source = "for i in range(10):\n    print(i)";
        let module = parse(source).unwrap();
        if let Node::For(stmt) = &module.items[0] {
            if let Pattern::Identifier(name) = &stmt.pattern {
                assert_eq!(name, "i");
            }
        } else {
            panic!("Expected for statement");
        }
    }

    #[test]
    fn test_while_loop() {
        let source = "while x > 0:\n    x = x - 1";
        let module = parse(source).unwrap();
        assert!(matches!(&module.items[0], Node::While(_)));
    }

    // === Pattern Tests ===

    #[test]
    fn test_tuple_pattern() {
        let source = "let (x, y) = point";
        let module = parse(source).unwrap();
        if let Node::Let(stmt) = &module.items[0] {
            if let Pattern::Tuple(patterns) = &stmt.pattern {
                assert_eq!(patterns.len(), 2);
            } else {
                panic!("Expected tuple pattern");
            }
        }
    }
}
