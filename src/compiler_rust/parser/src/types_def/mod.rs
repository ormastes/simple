//! Type definition parsing module
//!
//! This module contains parsing logic for type definitions:
//! - struct
//! - class
//! - enum
//! - trait
//! - impl
//! - actor

mod bitfield;
mod enum_parsing;
mod trait_impl_parsing;

use std::collections::HashMap;

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

        // Check for trait implementation syntax: struct Name(Trait):
        // This means the struct implements the given trait
        let implements_trait = if self.check(&TokenKind::LParen) {
            self.advance();
            let trait_name = self.expect_identifier()?;
            self.expect(&TokenKind::RParen)?;
            Some(trait_name)
        } else {
            None
        };

        let where_clause = self.parse_where_clause()?;

        // Check for empty struct (no body)
        // Empty structs are declared as just "struct Name" without a colon and body
        let (fields, methods, invariant, doc_comment) = if self.check(&TokenKind::Newline) || self.is_at_end() {
            // Empty struct - no fields, methods, invariant, or doc comment
            (Vec::new(), Vec::new(), None, None)
        } else {
            // Parse fields, optional inline methods, optional invariant, and doc comment
            self.parse_indented_fields_and_methods()?
        };

        let struct_def = StructDef {
            span: self.make_span(start_span),
            name: name.clone(),
            generic_params: generic_params.clone(),
            where_clause,
            fields,
            methods: methods.clone(),
            visibility: Visibility::Private,
            attributes,
            doc_comment,
            invariant,
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
        };

        // If struct implements a trait, generate both struct and impl nodes
        // For now, just store the trait in the struct for later processing
        // The compiler can generate the impl from methods marked with the trait
        if let Some(_trait_name) = implements_trait {
            // For now, treat methods in the struct body as trait implementations
            // This is simplified - a full implementation would generate an impl block
            Ok(Node::Struct(struct_def))
        } else {
            Ok(Node::Struct(struct_def))
        }
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

        // Check for empty class (no body)
        let (fields, methods, invariant, macro_invocations, mut mixins, doc_comment) =
            if self.check(&TokenKind::Newline) || self.is_at_end() {
                // Empty class - no fields, methods, invariant, etc.
                (Vec::new(), Vec::new(), None, Vec::new(), Vec::new(), None)
            } else {
                self.parse_class_body()?
            };

        // Prepend explicit mixins from `with` clause
        mixins.splice(0..0, explicit_mixins);

        Ok(Node::Class(ClassDef {
            span: self.make_span(start_span),
            name,
            generic_params: generic_params.clone(),
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
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
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
        let (fields, methods, _invariant, _macro_invocations, inner_mixins, doc_comment) = self.parse_class_body()?;

        // Merge `use` declarations from mixin body into required_mixins
        let mut all_required_mixins = required_mixins;
        for mref in &inner_mixins {
            if !all_required_mixins.contains(&mref.name) {
                all_required_mixins.push(mref.name.clone());
            }
        }

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
            required_mixins: all_required_mixins,
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
            } else if self.check(&TokenKind::Var) && self.peek_is(&TokenKind::Fn) {
                // Deprecated `var fn` syntax - emit warning and parse as mutable method
                use crate::error_recovery::{ErrorHint, ErrorHintLevel};
                let warning = ErrorHint {
                    level: ErrorHintLevel::Warning,
                    message: "Deprecated: `var fn` syntax".to_string(),
                    span: self.current.span,
                    suggestion: Some("Replace `var fn method()` with `me method()`".to_string()),
                    help: None,
                };
                self.error_hints.push(warning);
                self.advance(); // consume 'var'
                                // Now parse as mutable method (fn will be parsed next)
                let item = self.parse_item()?;
                if let Node::Function(mut f) = item {
                    f.is_me_method = true;
                    // Auto-inject 'self' parameter for instance methods if not present
                    if f.params.is_empty() || f.params[0].name != "self" {
                        let self_param = Parameter {
                            span: f.span,
                            name: "self".to_string(),
                            ty: None,
                            default: None,
                            mutability: Mutability::Immutable,
                            inject: false,
                            variadic: false,
                            call_site_label: None,
                        };
                        f.params.insert(0, self_param);
                    }
                    methods.push(f);
                }
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

                // Parse decorators first (@inject, @effect, etc.)
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    let decorator = self.parse_decorator()?;
                    decorators.push(decorator);
                    // Skip newlines after decorator
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                // Handle optional `pub` keyword after decorators
                let _is_pub2 = if self.check(&TokenKind::Pub) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Handle optional `static` keyword for static methods
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Handle static var/val as field declarations in struct body
                if is_static && (self.check(&TokenKind::Var) || self.check(&TokenKind::Val)) {
                    self.advance(); // consume var/val
                    // Skip the entire static field declaration until newline
                    while !self.check(&TokenKind::Newline)
                        && !self.check(&TokenKind::Dedent)
                        && !self.is_at_end()
                    {
                        self.advance();
                    }
                    self.skip_newlines();
                    continue;
                }

                // Parse the function (with decorators already parsed)
                let item = if decorators.is_empty() && !_is_pub2 {
                    self.parse_item()?
                } else {
                    // Parse function directly with decorators
                    self.parse_function_with_decorators(decorators)?
                };
                if let Node::Function(mut f) = item {
                    // Set the is_static flag on the function
                    f.is_static = is_static;

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
                            call_site_label: None,
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
            } else if self.check(&TokenKind::Val) || self.check(&TokenKind::Var) {
                // Skip val/var bindings inside struct bodies.
                // These are desugared type variables: `val _tv_0 = [[text], [text]]`
                // They define local type aliases used by subsequent fields.
                self.advance(); // consume val/var
                // Skip everything until the next newline (consume the whole binding)
                while !self.check(&TokenKind::Newline)
                    && !self.check(&TokenKind::Dedent)
                    && !self.is_at_end()
                {
                    self.advance();
                }
            } else if self.check(&TokenKind::Pass) {
                // pass/pass_dn/pass_do_nothing in struct body: skip as no-op
                self.advance();
                self.skip_newlines();
            } else if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "pass_dn" || name == "pass_do_nothing" || name == "pass_todo") {
                // pass_dn / pass_do_nothing / pass_todo as identifiers in struct body: skip
                self.advance();
                self.skip_newlines();
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
                || self.check(&TokenKind::Me)  // Mutable method keyword
                || self.check(&TokenKind::Async)
                || self.check(&TokenKind::At)
                || self.check(&TokenKind::Hash)
                || self.check(&TokenKind::Static)
                || (self.check(&TokenKind::Pub) && (self.peek_is(&TokenKind::Fn) || self.peek_is(&TokenKind::Async) || self.peek_is(&TokenKind::Me) || self.peek_is(&TokenKind::Static)))
            {
                let start_span = self.current.span;

                // Parse decorators first (@inject, @effect, etc.)
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    let decorator = self.parse_decorator()?;
                    decorators.push(decorator);
                    // Skip newlines after decorator
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                // Handle optional `pub` keyword after decorators
                let _is_pub = if self.check(&TokenKind::Pub) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Handle optional `static` keyword for static methods
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Handle optional `async` keyword after static (for static async methods)
                let is_async_after_static = if is_static && self.check(&TokenKind::Async) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Handle static var/val as field declarations in class body
                if is_static && (self.check(&TokenKind::Var) || self.check(&TokenKind::Val)) {
                    self.advance(); // consume var/val
                    // Skip the entire static field declaration until newline
                    while !self.check(&TokenKind::Newline)
                        && !self.check(&TokenKind::Dedent)
                        && !self.is_at_end()
                    {
                        self.advance();
                    }
                    self.skip_newlines();
                    continue;
                }

                // Parse the function (with decorators already parsed)
                // Only use parse_item() for non-static, non-decorated methods
                let mut item = if decorators.is_empty() && !_is_pub && !is_static {
                    self.parse_item()?
                } else {
                    // Parse function directly with decorators or for static methods
                    self.parse_function_with_decorators(decorators)?
                };
                // Add async effect if method is async (either async fn or static async fn)
                if is_async_after_static {
                    if let Node::Function(ref mut f) = item {
                        f.effects.push(crate::ast::Effect::Async);
                    }
                }
                if let Node::Function(mut f) = item {
                    // Set the is_static flag on the function
                    f.is_static = is_static;

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
                            call_site_label: None,
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
                // Deprecated `var fn` syntax - emit warning and parse as mutable method
                use crate::error_recovery::{ErrorHint, ErrorHintLevel};
                let warning = ErrorHint {
                    level: ErrorHintLevel::Warning,
                    message: "Deprecated: `var fn` syntax".to_string(),
                    span: self.current.span,
                    suggestion: Some("Replace `var fn method()` with `me method()`".to_string()),
                    help: None,
                };
                self.error_hints.push(warning);
                self.advance(); // consume 'var'
                let item = self.parse_item()?;
                if let Node::Function(mut f) = item {
                    f.is_me_method = true;
                    if f.params.is_empty() || f.params[0].name != "self" {
                        let self_param = Parameter {
                            span: f.span,
                            name: "self".to_string(),
                            ty: None,
                            default: None,
                            mutability: Mutability::Immutable,
                            inject: false,
                            variadic: false,
                            call_site_label: None,
                        };
                        f.params.insert(0, self_param);
                    }
                    methods.push(f);
                }
            } else if self.check(&TokenKind::Pass) {
                // pass/pass_dn/pass_do_nothing in class body: skip as no-op
                self.advance();
                self.skip_newlines();
            } else if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "pass_dn" || name == "pass_do_nothing" || name == "pass_todo") {
                // pass_dn / pass_do_nothing / pass_todo as identifiers in class body: skip
                self.advance();
                self.skip_newlines();
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

    /// Parse extend block: `extend TypeName: methods`
    /// Adds methods to an existing type (like Rust's impl blocks without traits).
    pub(crate) fn parse_extend(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Extend)?;

        let target_type = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;

        self.expect(&TokenKind::Colon)?;

        // Parse body with methods
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut methods = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            // Parse doc comment
            let doc_comment = self.try_parse_doc_comment();

            // Parse function definition
            if self.check(&TokenKind::Fn) || self.check(&TokenKind::Me) || self.check(&TokenKind::Static) {
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };

                let func_node = self.parse_function_with_doc(doc_comment)?;
                if let Node::Function(mut func_def) = func_node {
                    func_def.is_static = is_static;
                    methods.push(func_def);
                }
            } else {
                // Skip anything that isn't a function
                self.advance();
            }

            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Extend(ExtendBlock {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            target_type,
            generic_params,
            methods,
        }))
    }
}
