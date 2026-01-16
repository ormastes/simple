//! Type definition parsing module
//!
//! This module contains parsing logic for type definitions:
//! - struct
//! - class
//! - enum
//! - trait
//! - impl
//! - actor

mod enum_parsing;
mod trait_impl_parsing;

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::Parser;

impl<'a> Parser<'a> {
    // === Struct ===

    pub(crate) fn parse_struct(&mut self) -> Result<Node, ParseError> {
        self.parse_struct_with_attrs(vec![])
    }

    pub(crate) fn parse_struct_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Struct)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;
        let where_clause = self.parse_where_clause()?;
        // Parse fields, optional inline methods, optional invariant, and doc comment
        let (fields, methods, invariant, doc_comment) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Struct(StructDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            fields,
            methods,
            visibility: Visibility::Private,
            attributes,
            doc_comment,
            invariant,
        }))
    }

    // === Class ===

    pub(crate) fn parse_class(&mut self) -> Result<Node, ParseError> {
        self.parse_class_with_attrs(vec![])
    }

    pub(crate) fn parse_class_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Class)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;

        // Support both syntaxes for class inheritance:
        // - class Child(Parent):      (legacy syntax)
        // - class Child extends Parent:  (extends keyword syntax)
        let parent = if self.check(&TokenKind::LParen) {
            self.advance();
            let p = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(p)
        } else if self.check(&TokenKind::Extends) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            None
        };

        // Parse mixin application: class Name with Mixin1, Mixin2<T>:
        let mut explicit_mixins = Vec::new();
        if self.check(&TokenKind::With) {
            self.advance();
            loop {
                let mixin_name = self.expect_identifier()?;
                let type_args = if self.check(&TokenKind::Lt) {
                    self.parse_generic_args()?
                } else {
                    Vec::new()
                };

                explicit_mixins.push(MixinRef {
                    span: self.current.span,
                    name: mixin_name,
                    type_args,
                    overrides: Vec::new(),
                });

                if !self.check(&TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }

        let where_clause = self.parse_where_clause()?;
        let (fields, methods, invariant, macro_invocations, mut mixins, doc_comment) = self.parse_class_body()?;

        // Prepend explicit mixins from `with` clause
        mixins.splice(0..0, explicit_mixins);

        Ok(Node::Class(ClassDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            fields,
            methods,
            parent,
            visibility: Visibility::Private,
            effects: Vec::new(), // Effects are added via decorators during parsing
            attributes,
            doc_comment,
            invariant,
            macro_invocations,
            mixins,
        }))
    }

    // === Mixin ===

    pub(crate) fn parse_mixin(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mixin)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;

        // Parse optional requires clause: requires Trait1, Trait2
        let (required_traits, required_mixins) = if self.check(&TokenKind::Requires) {
            self.advance();
            self.parse_mixin_requirements()?
        } else {
            (Vec::new(), Vec::new())
        };

        let _where_clause = self.parse_where_clause()?;
        let (fields, methods, _invariant, _macro_invocations, _mixins, doc_comment) = self.parse_class_body()?;

        // Parse required methods (methods without bodies)
        let required_methods = methods
            .iter()
            .filter(|m| m.is_abstract)
            .map(|m| RequiredMethodSig {
                span: m.span,
                name: m.name.clone(),
                params: m.params.clone(),
                return_type: m.return_type.clone(),
            })
            .collect();

        let methods: Vec<_> = methods.into_iter().filter(|m| !m.is_abstract).collect();

        Ok(Node::Mixin(MixinDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            required_traits,
            required_mixins,
            fields,
            methods,
            required_methods,
            visibility: Visibility::Private,
            doc_comment,
        }))
    }

    fn parse_mixin_requirements(&mut self) -> Result<(Vec<String>, Vec<String>), ParseError> {
        let mut required_traits = Vec::new();
        let mut required_mixins = Vec::new();

        loop {
            let req = self.expect_identifier()?;
            // Simple heuristic: if it starts with uppercase, it's a trait; otherwise, mixin
            // This is a simplification; real implementation might need type resolution
            if req.chars().next().unwrap().is_uppercase() {
                required_traits.push(req);
            } else {
                required_mixins.push(req);
            }

            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance();
        }

        Ok((required_traits, required_mixins))
    }

    fn parse_generic_args(&mut self) -> Result<Vec<Type>, ParseError> {
        self.expect(&TokenKind::Lt)?;
        let mut args = Vec::new();
        loop {
            args.push(self.parse_type()?);
            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance();
        }
        self.expect(&TokenKind::Gt)?;
        Ok(args)
    }

    // === Actor ===

    pub(crate) fn parse_actor(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Actor)?;
        let name = self.expect_identifier()?;

        let (fields, methods, _invariant, _doc_comment) = self.parse_indented_fields_and_methods()?;

        Ok(Node::Actor(ActorDef {
            span: self.make_span(start_span),
            name,
            fields,
            methods,
            visibility: Visibility::Private,
        }))
    }

    // === Field (shared by struct, class, actor) ===

    pub(crate) fn parse_field(&mut self) -> Result<Field, ParseError> {
        let start_span = self.current.span;

        let visibility = if self.check(&TokenKind::Pub) {
            self.advance();
            Visibility::Public
        } else {
            Visibility::Private
        };

        let mutability = if self.check(&TokenKind::Mut) {
            self.advance();
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };

        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;

        let default = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(Field {
            span: self.make_span(start_span),
            name,
            ty,
            default,
            mutability,
            visibility,
        })
    }

    // === Helper methods to reduce duplication ===

    /// Create a span from start_span to the current position
    fn make_span(&self, start_span: Span) -> Span {
        Span::new(
            start_span.start,
            self.previous.span.end,
            start_span.line,
            start_span.column,
        )
    }

    /// Skip newlines until we hit a non-newline token
    pub(crate) fn skip_newlines(&mut self) {
        while self.check(&TokenKind::Newline) {
            self.advance();
        }
    }

    /// Consume dedent if present
    fn consume_dedent(&mut self) {
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }
    }

    /// Parse a colon-newline-indent sequence
    fn expect_block_start(&mut self) -> Result<(), ParseError> {
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        Ok(())
    }

    /// Parse indented items with a custom parser function
    fn parse_indented_items<T, F>(&mut self, mut parse_item: F) -> Result<Vec<T>, ParseError>
    where
        F: FnMut(&mut Self) -> Result<T, ParseError>,
    {
        let mut items = Vec::new();
        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_indented_items")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            items.push(parse_item(self)?);
        }
        self.consume_dedent();
        Ok(items)
    }

    /// Parse fields in an indented block (struct)
    #[allow(dead_code)]
    fn parse_indented_fields(&mut self) -> Result<Vec<Field>, ParseError> {
        self.expect_block_start()?;
        self.parse_indented_items(|p| p.parse_field())
    }

    /// Parse fields and methods in an indented block (class, actor, struct)
    fn parse_indented_fields_and_methods(
        &mut self,
    ) -> Result<(Vec<Field>, Vec<FunctionDef>, Option<InvariantBlock>, Option<DocComment>), ParseError> {
        self.debug_enter("parse_indented_fields_and_methods");
        self.expect_block_start()?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut invariant = None;
        let mut doc_comment = None;

        // Capture docstring if present (first item after indent)
        // Accept both plain strings and FStrings (double-quoted strings become FStrings)
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

        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_indented_fields_and_methods")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Invariant) {
                // Parse invariant block (only one allowed)
                if invariant.is_some() {
                    return Err(ParseError::syntax_error_with_span(
                        "Multiple invariant blocks not allowed",
                        self.current.span,
                    ));
                }
                invariant = self.parse_invariant_block()?;
            } else if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Me)  // Mutable method keyword
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || self.check(&TokenKind::Static)
                || (self.check(&TokenKind::Pub) && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async) || self.peek_is(&TokenKind::Me)))
            {
                // Method (optionally async/decorated/attributed/pub/static).
                let start_span = self.current.span;
                // Handle optional `static` keyword for static methods
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };
                let item = self.parse_item()?;
                if let Node::Function(mut f) = item {
                    // Auto-inject 'self' parameter for instance methods (non-static) if not present
                    // Skip auto-injection for constructors (methods named "new")
                    if !is_static && f.name != "new" && (f.params.is_empty() || f.params[0].name != "self") {
                        // Inject implicit self parameter at the beginning
                        let self_param = Parameter {
                            span: f.span,
                            name: "self".to_string(),
                            ty: None, // Type is implicit (will be inferred as the struct/class type)
                            default: None,
                            mutability: Mutability::Immutable,
                            inject: false,
                            variadic: false,
                        };
                        f.params.insert(0, self_param);
                    }
                    methods.push(f);
                } else {
                    return Err(ParseError::syntax_error_with_span(
                        "Expected method definition in class body",
                        start_span,
                    ));
                }
            } else {
                // Field (may be public: pub field_name: Type)
                fields.push(self.parse_field()?);
            }
        }
        self.consume_dedent();
        self.debug_exit("parse_indented_fields_and_methods");
        Ok((fields, methods, invariant, doc_comment))
    }

    /// Parse fields, methods, and macro invocations in a class body
    fn parse_class_body(
        &mut self,
    ) -> Result<
        (
            Vec<Field>,
            Vec<FunctionDef>,
            Option<InvariantBlock>,
            Vec<MacroInvocation>,
            Vec<MixinRef>,
            Option<DocComment>,
        ),
        ParseError,
    > {
        self.debug_enter("parse_class_body");
        self.expect_block_start()?;
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let mut invariant = None;
        let mut macro_invocations = Vec::new();
        let mut mixins = Vec::new();
        let mut doc_comment = None;

        // Capture docstring if present (first item after indent)
        // Accept both plain strings and FStrings (double-quoted strings become FStrings)
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

        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_class_body")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }

            if self.check(&TokenKind::Invariant) {
                if invariant.is_some() {
                    return Err(ParseError::syntax_error_with_span(
                        "Multiple invariant blocks not allowed",
                        self.current.span,
                    ));
                }
                invariant = self.parse_invariant_block()?;
            } else if self.check(&TokenKind::Use) {
                // Mixin application: use MixinName, MixinName2
                self.advance();
                loop {
                    let start_span = self.current.span;
                    let name = self.expect_identifier()?;
                    let type_args = if self.check(&TokenKind::Lt) {
                        self.parse_generic_args()?
                    } else {
                        Vec::new()
                    };
                    mixins.push(MixinRef {
                        span: self.make_span(start_span),
                        name,
                        type_args,
                        overrides: Vec::new(),
                    });
                    if !self.check(&TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
                self.skip_newlines();
            } else if self.check(&TokenKind::Fn)
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || self.check(&TokenKind::Static)
                || (self.check(&TokenKind::Pub) && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async)))
            {
                let start_span = self.current.span;
                // Handle optional `static` keyword for static methods
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };
                let item = self.parse_item()?;
                if let Node::Function(mut f) = item {
                    // Auto-inject 'self' parameter for instance methods (non-static) if not present
                    // Skip auto-injection for constructors (methods named "new")
                    if !is_static && f.name != "new" && (f.params.is_empty() || f.params[0].name != "self") {
                        // Inject implicit self parameter at the beginning
                        let self_param = Parameter {
                            span: f.span,
                            name: "self".to_string(),
                            ty: None, // Type is implicit (will be inferred as the class type)
                            default: None,
                            mutability: Mutability::Immutable,
                            inject: false,
                            variadic: false,
                        };
                        f.params.insert(0, self_param);
                    }
                    methods.push(f);
                } else {
                    return Err(ParseError::syntax_error_with_span(
                        "Expected method definition in class body",
                        start_span,
                    ));
                }
            } else if self.is_macro_invocation_start() {
                // Macro invocation: macro_name!(args)
                macro_invocations.push(self.parse_class_body_macro_invocation()?);
            } else if self.check(&TokenKind::Var) && self.peek_is(&TokenKind::Fn) {
                // Common mistake: `var fn` instead of `me` for mutable methods
                return Err(ParseError::syntax_error_with_span(
                    "Use `me` keyword instead of `var fn` for mutable methods. Example: `me update(x: i32):` instead of `var fn update(x: i32):`",
                    self.current.span,
                ));
            } else {
                fields.push(self.parse_field()?);
            }
        }
        self.consume_dedent();
        self.debug_exit("parse_class_body");
        Ok((fields, methods, invariant, macro_invocations, mixins, doc_comment))
    }

    /// Check if current position is at a macro invocation (identifier followed by !)
    fn is_macro_invocation_start(&mut self) -> bool {
        if let TokenKind::Identifier { .. } = &self.current.kind {
            self.peek_is(&TokenKind::Bang)
        } else {
            false
        }
    }

    /// Parse a macro invocation in a class body: name!(args)
    fn parse_class_body_macro_invocation(&mut self) -> Result<MacroInvocation, ParseError> {
        let start_span = self.current.span;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Bang)?;
        let args = self.parse_macro_args()?;

        // Consume optional newline after macro invocation
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(MacroInvocation {
            span: self.make_span(start_span),
            name,
            args,
        })
    }
}
