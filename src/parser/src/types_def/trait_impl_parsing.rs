// Trait and Impl block parsing
//
// This module handles:
// - Trait definition parsing
// - Impl block parsing
// - Interface binding parsing (static polymorphism)
// - Associated type parsing (declarations and implementations)
// - Trait method parsing (abstract and default implementations)

use crate::ast::*;
use crate::error::ParseError;
use crate::token::TokenKind;

use super::super::Parser;

impl<'a> Parser<'a> {
    // === Trait ===

    pub(crate) fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;
        let where_clause = self.parse_where_clause()?;

        let (associated_types, methods) = self.parse_indented_trait_body()?;

        Ok(Node::Trait(TraitDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            where_clause,
            associated_types,
            methods,
            visibility: Visibility::Private,
            doc_comment: None,
        }))
    }

    // === Impl ===

    pub(crate) fn parse_impl(&mut self) -> Result<Node, ParseError> {
        self.parse_impl_with_attrs(Vec::new())
    }

    pub(crate) fn parse_impl_with_attrs(
        &mut self,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        // Parse optional generic params for impl block: impl<T> Trait for Type<T>
        let generic_params = self.parse_generic_params_as_strings()?;

        // Parse the first type (could be trait name or target type)
        let first_type = self.parse_type()?;

        let (trait_name, target_type) = if self.check(&TokenKind::For) {
            // impl Trait for Type pattern
            self.advance();
            let target = self.parse_type()?;
            // Extract simple name from first_type for trait_name
            let trait_name_str = match &first_type {
                Type::Simple(name) | Type::Generic { name, .. } => name.clone(),
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        expected: "simple trait name".to_string(),
                        found: format!("{:?}", first_type),
                        span: self.current.span.clone(),
                    })
                }
            };
            (Some(trait_name_str), target)
        } else {
            // impl Type pattern (inherent impl)
            (None, first_type)
        };

        let where_clause = self.parse_where_clause()?;
        let (associated_types, methods) = self.parse_indented_impl_body()?;

        Ok(Node::Impl(ImplBlock {
            span: self.make_span(start_span),
            attributes,
            generic_params,
            target_type,
            trait_name,
            where_clause,
            associated_types,
            methods,
        }))
    }

    // === Interface Binding (Static Polymorphism) ===

    /// Parse an interface binding: `bind Interface = ImplType`
    /// Binds a trait to a concrete implementation for static dispatch.
    pub(crate) fn parse_interface_binding(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Bind)?;

        // Parse interface name
        let interface_name = self.expect_identifier()?;

        // Expect '='
        self.expect(&TokenKind::Assign)?;

        // Parse implementation type
        let impl_type = self.parse_type()?;

        Ok(Node::InterfaceBinding(InterfaceBinding {
            span: self.make_span(start_span),
            interface_name,
            impl_type,
            doc_comment: None,
        }))
    }

    // === Impl body parsing ===

    /// Parse methods in an indented block (impl only - all methods must have bodies)
    /// Parse impl body: associated type implementations and methods
    pub(crate) fn parse_indented_impl_body(
        &mut self,
    ) -> Result<(Vec<AssociatedTypeImpl>, Vec<FunctionDef>), ParseError> {
        self.debug_enter("parse_indented_impl_body");
        self.expect_block_start()?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_indented_impl_body")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Check for associated type impl: `type Item = i64`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_impl()?);
            } else {
                // Handle optional `pub` visibility prefix for methods
                let visibility = if self.check(&TokenKind::Pub) {
                    self.advance();
                    crate::ast::Visibility::Public
                } else {
                    crate::ast::Visibility::Private
                };
                // Handle optional `static` keyword for static methods
                let is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };
                // Handle async functions and me methods in impl blocks
                let item = if self.check(&TokenKind::Async) {
                    self.parse_async_function()?
                } else {
                    // Handles both 'fn' and 'me' keywords
                    self.parse_function()?
                };
                if let Node::Function(mut f) = item {
                    f.visibility = visibility;
                    // Auto-inject 'self' parameter for instance methods (non-static) if not present
                    if !is_static && (f.params.is_empty() || f.params[0].name != "self") {
                        // Inject implicit self parameter at the beginning
                        let self_param = Parameter {
                            span: f.span,
                            name: "self".to_string(),
                            ty: None, // Type is implicit (will be inferred as the impl type)
                            default: None,
                            mutability: crate::ast::Mutability::Immutable,
                            inject: false,
                        };
                        f.params.insert(0, self_param);
                    }
                    methods.push(f);
                }
            }
        }
        self.consume_dedent();
        self.debug_exit("parse_indented_impl_body");
        Ok((associated_types, methods))
    }

    /// Parse associated type implementation in an impl block
    /// `type Item = i64`
    fn parse_associated_type_impl(&mut self) -> Result<AssociatedTypeImpl, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;

        // Consume newline
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(AssociatedTypeImpl {
            span: self.make_span(start_span),
            name,
            ty,
        })
    }

    /// Parse methods only (legacy)
    #[allow(dead_code)]
    fn parse_indented_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        let (_, methods) = self.parse_indented_impl_body()?;
        Ok(methods)
    }

    // === Trait body parsing ===

    /// Parse trait body: associated types and methods
    pub(crate) fn parse_indented_trait_body(
        &mut self,
    ) -> Result<(Vec<AssociatedTypeDef>, Vec<FunctionDef>), ParseError> {
        self.expect_block_start()?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_indented_trait_body")?;
            iterations += 1;

            self.skip_newlines();
            if self.check(&TokenKind::Dedent) {
                break;
            }
            // Check for associated type: `type Name` or `type Name: Bound` or `type Name = Default`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_def()?);
            } else {
                // Handle async methods in trait blocks
                let is_async = self.check(&TokenKind::Async);
                if is_async {
                    self.advance();
                }
                let mut method = self.parse_trait_method()?;
                if is_async {
                    method.effects.push(crate::ast::Effect::Async);
                }
                methods.push(method);
            }
        }
        self.consume_dedent();
        Ok((associated_types, methods))
    }

    /// Parse associated type declaration in a trait
    /// `type Item` or `type Item: Clone` or `type Item = i64`
    fn parse_associated_type_def(&mut self) -> Result<AssociatedTypeDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Type)?;
        let name = self.expect_identifier()?;

        // Parse optional bounds: `type Item: Clone + Default`
        let bounds = if self.check(&TokenKind::Colon) {
            self.advance();
            let mut bounds = Vec::new();
            bounds.push(self.expect_identifier()?);
            while self.check(&TokenKind::Plus) {
                self.advance();
                bounds.push(self.expect_identifier()?);
            }
            bounds
        } else {
            Vec::new()
        };

        // Parse optional default: `type Item = i64`
        let default = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Consume newline
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        Ok(AssociatedTypeDef {
            span: self.make_span(start_span),
            name,
            bounds,
            default,
        })
    }

    /// Parse trait methods in an indented block (can be abstract or have default impl)
    /// Legacy function for backwards compatibility
    #[allow(dead_code)]
    fn parse_indented_trait_methods(&mut self) -> Result<Vec<FunctionDef>, ParseError> {
        let (_, methods) = self.parse_indented_trait_body()?;
        Ok(methods)
    }

    /// Parse a single trait method (can be abstract or have default implementation)
    /// Abstract: `fn foo(self) -> i64` (ends with newline)
    /// Default:  `fn foo(self) -> i64:\n    return 0`
    fn parse_trait_method(&mut self) -> Result<FunctionDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let where_clause = self.parse_where_clause()?;

        // Check if this is an abstract method (newline) or has default body (colon)
        let (body, is_abstract) =
            if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
                // Abstract method - no body
                if self.check(&TokenKind::Newline) {
                    self.advance();
                }
                (Block::default(), true)
            } else {
                // Default implementation - has body
                self.expect(&TokenKind::Colon)?;
                (self.parse_block()?, false)
            };

        Ok(FunctionDef {
            span: self.make_span(start_span),
            name,
            generic_params,
            params,
            return_type,
            where_clause,
            body,
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract,
            is_sync: false,
            bounds_block: None,
        })
    }
}
