//! Function parsing
//!
//! This module handles parsing of function definitions, including decorators,
//! attributes, doc comments, and contract blocks.

use std::collections::HashMap;

use crate::ast::*;
use crate::effect_inference::has_suspension_in_body;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

impl<'a> Parser<'a> {
    pub(crate) fn parse_async_function(&mut self) -> Result<Node, ParseError> {
        self.advance(); // consume 'async'
        let mut func = self.parse_function()?;
        if let Node::Function(ref mut f) = func {
            f.effects.push(Effect::Async);
        }
        Ok(func)
    }

    pub(crate) fn parse_sync_function(&mut self) -> Result<Node, ParseError> {
        self.advance(); // consume 'sync'
        let mut func = self.parse_function()?;
        if let Node::Function(ref mut f) = func {
            f.is_sync = true;

            // Validate: sync functions cannot use suspension operators
            if crate::effect_inference::has_suspension_in_body(&f.body) {
                return Err(ParseError::syntax_error_with_span(
                    format!(
                        "Suspension operators (~=, if~, while~, etc.) are not allowed in sync functions.\n\
                         Function '{}' is marked as 'sync' but contains suspension operators.\n\
                         \n\
                         To fix:\n\
                         - Remove the 'sync' keyword to allow async behavior, OR\n\
                         - Remove suspension operators from the function body",
                        f.name
                    ),
                    f.span,
                ));
            }
        }
        Ok(func)
    }

    pub(crate) fn parse_function(&mut self) -> Result<Node, ParseError> {
        self.parse_function_with_decorators(vec![])
    }

    pub(crate) fn parse_function_with_decorators(&mut self, decorators: Vec<Decorator>) -> Result<Node, ParseError> {
        self.parse_function_with_attrs(decorators, vec![])
    }

    pub(super) fn parse_function_with_attrs(
        &mut self,
        decorators: Vec<Decorator>,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Accept both 'fn' and 'me' keywords
        // 'me' indicates a mutable method (modifies self)
        // Also accept 'me fn' as equivalent to 'me'
        let mut is_generator = false;
        let is_me_method = if self.check(&TokenKind::Me) {
            self.advance();
            // Optionally consume 'fn' after 'me' (me fn is equivalent to me)
            if self.check(&TokenKind::Fn) {
                self.advance();
            }
            true
        } else if self.check(&TokenKind::Gen) {
            is_generator = true;
            self.advance();
            false
        } else if self.check(&TokenKind::Kernel) {
            self.advance();
            false
        } else {
            self.expect(&TokenKind::Fn)?;
            false
        };

        // Allow keywords like 'new', 'type', etc. as function names
        let name = self.expect_method_name()?;
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params_as_strings()?;
        let params = self.parse_parameters()?;

        // Skip newlines/indents for multi-line function signatures:
        //   fn name(params)
        //       -> ReturnType:
        let sig_indents = if self.peek_through_newlines_and_indents_is(&TokenKind::Arrow) {
            self.skip_newlines_and_indents_for_method_chain()
        } else {
            0
        };

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Parse optional return constraint for dependent types (VER-011):
        // `fn f(x: T) -> U where result.len() == x.len():`
        // This is distinguished from trait bounds by checking if the where clause
        // starts with 'result' identifier (expression) vs 'TypeParam:' (trait bound)
        let return_constraint = self.parse_return_constraint()?;

        // Parse optional where clause: where T: Clone + Default
        let where_clause = self.parse_where_clause()?;

        // Skip newlines before the function body colon or abstract semicolon
        self.skip_newlines();
        // Consume any dedents from multi-line signature
        if sig_indents > 0 {
            self.consume_dedents_for_method_chain(sig_indents);
        }

        // Check for abstract/extern method (semicolon instead of body, or no body at all)
        let is_abstract = if self.check(&TokenKind::Semicolon) {
            self.advance();
            true
        } else if !self.check(&TokenKind::Colon) {
            // No colon means bodyless declaration (e.g., @extern fn foo() -> T)
            true
        } else {
            false
        };

        let (body, contract, bounds_block) = if is_abstract {
            // Abstract method has no body
            let empty_span = Span::new(start_span.start, start_span.end, start_span.line, start_span.column);
            (
                Block {
                    span: empty_span,
                    statements: vec![],
                },
                None,
                None,
            )
        } else {
            self.expect(&TokenKind::Colon)?;

            // Check for single-line vs block function syntax
            if self.check(&TokenKind::Newline) {
                // Block form: fn name(): \n INDENT body
                self.expect(&TokenKind::Newline)?;

                // For multiline signatures where the colon is on the indented line
                // (e.g., `fn foo()\n    -> T:\n    body`), the body is at the same
                // indent level as the arrow, so no additional Indent token appears.
                // In that case, skip the Indent expectation.
                if self.check(&TokenKind::Indent) {
                    self.advance();
                } else if sig_indents == 0 {
                    // Only require indent for normal (non-multiline-sig) functions
                    self.expect(&TokenKind::Indent)?;
                }
                // else: sig_indents > 0 means body at sig continuation level, no Indent expected

                // Parse optional contract block at the start of the function body
                // (new: in/out/out_err/invariant/decreases, legacy: requires/ensures)
                let contract = if self.check(&TokenKind::In)
                    || self.check(&TokenKind::Invariant)
                    || self.check(&TokenKind::Out)
                    || self.check(&TokenKind::OutErr)
                    || self.check(&TokenKind::Requires)
                    || self.check(&TokenKind::Ensures)
                    || self.check(&TokenKind::Decreases)
                {
                    self.parse_contract_block()?
                } else {
                    None
                };

                // Parse the rest of the function body statements
                let body = self.parse_block_body()?;

                // Check for trailing bounds: block (only valid for @simd decorated functions)
                let has_simd = decorators
                    .iter()
                    .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "simd"));

                let bounds_block = if has_simd {
                    // Skip newlines after body to check for bounds:
                    self.skip_newlines();
                    self.parse_bounds_block()?
                } else {
                    None
                };

                (body, contract, bounds_block)
            } else {
                // Single-line form: fn name(): expr
                // Parse the expression as the function body
                let expr_start = self.current.span;
                let expr = self.parse_expression()?;
                let expr_end = self.previous.span;

                // Wrap the expression in a Block with a single Expression statement
                let body = Block {
                    span: Span::new(expr_start.start, expr_end.end, expr_start.line, expr_start.column),
                    statements: vec![Node::Expression(expr)],
                };

                // Single-line functions don't support contracts or bounds blocks
                (body, None, None)
            }
        };

        // Effect inference: if body contains suspension operators, infer async effect
        let inferred_effects = if !is_abstract && has_suspension_in_body(&body) {
            vec![Effect::Async]
        } else {
            vec![]
        };

        Ok(Node::Function(FunctionDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            generic_params: generic_params.clone(),
            params,
            return_type,
            where_clause,
            body,
            visibility: Visibility::Private,
            effects: inferred_effects,
            decorators,
            attributes,
            doc_comment: None,
            contract,
            is_abstract,
            is_sync: false,
            is_static: false,
            is_me_method,
            is_generator,
            bounds_block,
            return_constraint,
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
        }))
    }

    /// Parse optional return constraint for dependent function types (VER-011)
    ///
    /// Syntax: `fn f(x: T) -> U where result.len() == x.len():`
    ///
    /// This is distinguished from trait bounds by checking if the where clause
    /// starts with 'result' identifier. Return constraints are expressions that
    /// reference `result` (the return value) and function parameters.
    fn parse_return_constraint(&mut self) -> Result<Option<Expr>, ParseError> {
        if !self.check(&TokenKind::Where) {
            return Ok(None);
        }

        // Peek ahead to see if this looks like a return constraint (expression)
        // or a trait bound (TypeParam: Trait)
        // Use peek_is to check if next token is 'result' identifier
        // If we see 'where result...' it's a return constraint
        // If we see 'where T:' it's a trait bound

        // Save state to peek ahead
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();

        self.advance(); // consume 'where'

        // Check if this is 'result' identifier (return constraint)
        let is_return_constraint = matches!(
            &self.current.kind,
            TokenKind::Identifier { name, .. } if name == "result"
        );

        if is_return_constraint {
            // Parse the constraint expression (e.g., result.len() == x.len())
            let expr = self.parse_expression()?;
            Ok(Some(expr))
        } else {
            // Not a return constraint - restore state for trait bound parsing
            self.pending_tokens.push_front(self.current.clone());
            self.current = saved_current;
            self.previous = saved_previous;
            Ok(None)
        }
    }

    /// Parse optional where clause: `where T: Trait1 + Trait2, U: Other`
    /// Supports associated type constraints: `where T: Add<Output=T>`
    pub(crate) fn parse_where_clause(&mut self) -> Result<WhereClause, ParseError> {
        if !self.check(&TokenKind::Where) {
            return Ok(vec![]);
        }

        self.advance(); // consume 'where'
        let mut bounds = Vec::new();

        loop {
            let span = self.current.span;
            let type_param = self.expect_identifier()?;

            self.expect(&TokenKind::Colon)?;

            // Parse trait bounds: Trait1 + Trait2<Output=T> + !Trait3 + ...
            // Each bound is parsed as a full type expression to support generics
            let mut trait_bounds = Vec::new();
            let mut negative_trait_bounds = Vec::new();
            loop {
                // Check for negative bound (!Trait)
                let is_negative = if self.check(&TokenKind::Bang) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Parse the bound as a full type expression
                // This handles: Clone, Iterator<Item=T>, Add<Output=Self>, etc.
                let bound_type = self.parse_type()?;

                if is_negative {
                    negative_trait_bounds.push(bound_type);
                } else {
                    trait_bounds.push(bound_type);
                }

                // Check for + to continue parsing bounds
                if self.check(&TokenKind::Plus) {
                    self.advance();
                } else {
                    break;
                }
            }

            bounds.push(WhereBound {
                span,
                type_param,
                bounds: trait_bounds,
                negative_bounds: negative_trait_bounds,
            });

            // Check for comma to continue parsing more bounds
            if self.check(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }

        Ok(bounds)
    }

    // === Doc Comment Variants ===

    pub(crate) fn parse_function_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_async_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_async_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_sync_function_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_sync_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_decorated_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
        let mut node = self.parse_decorated_function()?;
        if let Node::Function(ref mut f) = node {
            f.doc_comment = doc_comment;
        }
        Ok(node)
    }

    /// Parse a literal function definition: `literal fn _suffix(s: text) -> Type: body`
    ///
    /// Literal functions provide explicit control over suffix → type mapping.
    /// When a string literal like "value"_suffix is encountered, the literal function
    /// is called with the string value.
    ///
    /// # Syntax
    /// ```simple
    /// literal fn _re(s: text) -> Regex:
    ///     Regex.compile(s)
    /// ```
    pub(crate) fn parse_literal_function(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Literal)?;
        self.expect(&TokenKind::Fn)?;

        // Expect an identifier starting with underscore (the suffix name)
        let suffix_token = self.expect_identifier()?;
        if !suffix_token.starts_with('_') {
            return Err(ParseError::syntax_error_with_span(
                format!(
                    "Literal function name must start with underscore (e.g., _re, _ip), got '{}'",
                    suffix_token
                ),
                self.previous.span,
            ));
        }

        // Extract suffix without leading underscore
        let suffix = suffix_token[1..].to_string();

        // Parse parameters - expect exactly one parameter of type text
        self.expect(&TokenKind::LParen)?;
        let param_name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let param_type = self.parse_type()?;
        self.expect(&TokenKind::RParen)?;

        // Validate parameter type is text
        if let Type::Simple(type_name) = &param_type {
            if type_name != "text" && type_name != "str" && type_name != "String" {
                return Err(ParseError::syntax_error_with_span(
                    format!("Literal function parameter must be of type 'text', got '{}'", type_name),
                    self.previous.span,
                ));
            }
        }

        // Parse optional return type
        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Expect colon and body
        self.expect(&TokenKind::Colon)?;

        // Check for single-line vs block function syntax
        let body = if self.check(&TokenKind::Newline) {
            // Block form: literal fn _suffix(): \n INDENT body
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;
            self.parse_block_body()?
        } else {
            // Single-line form: literal fn _suffix(): expr
            let expr_start = self.current.span;
            let expr = self.parse_expression()?;
            let expr_end = self.previous.span;

            Block {
                span: Span::new(expr_start.start, expr_end.end, expr_start.line, expr_start.column),
                statements: vec![Node::Expression(expr)],
            }
        };

        Ok(Node::LiteralFunction(LiteralFunctionDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            suffix,
            param_name,
            return_type,
            body,
            doc_comment: None,
        }))
    }

    /// Parse a decorated function or impl block: @decorator fn foo(): ... or @default impl Trait for T:
    /// Effect decorators (@pure, @io, @net, @fs, @unsafe, @async) are extracted
    /// into the function's effects field; other decorators remain in decorators field.
    /// For impl blocks, @default is converted to #[default] attribute.
    pub(super) fn parse_decorated_function(&mut self) -> Result<Node, ParseError> {
        let mut decorators = Vec::new();
        let mut effects = Vec::new();
        let mut impl_attributes = Vec::new();

        // Parse all decorators (can be multiple: @pure @io fn foo)
        while self.check(&TokenKind::At) {
            let decorator = self.parse_decorator()?;

            // Check if this is an effect decorator
            if let Expr::Identifier(name) = &decorator.name {
                if let Some(effect) = Effect::from_decorator_name(name) {
                    effects.push(effect);
                    // Skip newlines after effect decorator
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    // Skip Indent if the decorated item is on a deeper indentation level
                    // e.g., @section("...") followed by indented val/const
                    if self.check(&TokenKind::Indent) {
                        self.advance();
                    }
                    continue;
                }

                // Check for @default before impl - convert to #[default] attribute
                if name == "default" {
                    impl_attributes.push(Attribute {
                        span: decorator.span,
                        name: "default".to_string(),
                        value: None,
                        args: None,
                    });
                    // Skip newlines after @default
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                    if self.check(&TokenKind::Indent) {
                        self.advance();
                    }
                    continue;
                }
            }

            // Not an effect decorator - keep as regular decorator
            decorators.push(decorator);

            // Skip newlines between decorators
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            // Skip Indent if the decorated item is on a deeper indentation level
            // Handles: @decorator\n    val/fn/class on indented line
            if self.check(&TokenKind::Indent) {
                self.advance();
            }
        }

        // Check if this is an impl block with @default decorator
        if self.check(&TokenKind::Impl) && !impl_attributes.is_empty() {
            return self.parse_impl_with_attrs(impl_attributes);
        }

        // Handle optional `pub` keyword before function
        let _is_pub = if self.check(&TokenKind::Pub) {
            self.advance();
            true
        } else {
            false
        };

        // Decorators can apply to extern, class, struct, enum etc. not just functions
        if self.check(&TokenKind::Extern) {
            let attrs: Vec<crate::ast::Attribute> = decorators
                .iter()
                .map(|d| {
                    let name = match &d.name {
                        crate::ast::Expr::Identifier(n) => n.clone(),
                        crate::ast::Expr::Call { callee, .. } => {
                            if let crate::ast::Expr::Identifier(n) = callee.as_ref() {
                                n.clone()
                            } else {
                                "decorator".to_string()
                            }
                        }
                        _ => "decorator".to_string(),
                    };
                    crate::ast::Attribute {
                        span: d.span,
                        name,
                        value: None,
                        args: None,
                    }
                })
                .collect();
            return self.parse_extern_with_attrs(attrs);
        }

        if self.check(&TokenKind::Class) {
            return self.parse_class();
        }

        if self.check(&TokenKind::Struct) {
            return self.parse_struct();
        }

        if self.check(&TokenKind::Enum) {
            return self.parse_enum();
        }

        if self.check(&TokenKind::Impl) {
            return self.parse_impl();
        }

        // Handle decorated non-function items:
        // @cfg(...) export ..., @cfg(...) use ..., @cfg(...) var ..., etc.
        // @section("...") val ..., @align(N) val ..., @cfg(...) const ..., etc.
        // @cfg("target_feature", "thumb") asm volatile(...) - conditional asm in function bodies
        // Skip the decorators (they're metadata for the compiler) and parse the item
        if self.check(&TokenKind::Export)
            || self.check(&TokenKind::Use)
            || self.check(&TokenKind::Var)
            || self.check(&TokenKind::Val)
            || self.check(&TokenKind::Mod)
            || self.check(&TokenKind::Trait)
            || self.check(&TokenKind::Union)
            || self.check(&TokenKind::Mixin)
            || self.check(&TokenKind::Const)
            || self.check(&TokenKind::Static)
            || self.check(&TokenKind::Type)
            || self.check(&TokenKind::From)
            || self.check(&TokenKind::Import)
            || self.check(&TokenKind::Asm)
        {
            // Decorators like @cfg don't apply to these items in our compilation model,
            // so we just parse the item normally
            return self.parse_item();
        }

        // Handle decorator followed by empty block (e.g., @decorator \n Dedent)
        // This can happen in stub files or conditional compilation
        if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
            return Ok(Node::Pass(crate::ast::PassStmt { span: self.current.span }));
        }

        // Now parse the function with the collected decorators and effects
        let mut node = self.parse_function_with_decorators(decorators)?;

        // Set the effects on the function
        if let Node::Function(ref mut f) = node {
            f.effects = effects;
        }

        Ok(node)
    }
}
