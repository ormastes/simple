// Trait and Impl block parsing
//
// This module handles:
// - Trait definition parsing
// - Impl block parsing
// - Interface binding parsing (static polymorphism)
// - Associated type parsing (declarations and implementations)
// - Trait method parsing (abstract and default implementations)

use std::collections::HashMap;

use crate::ast::*;
use crate::error::ParseError;
use crate::token::TokenKind;

use super::super::Parser;

/// Check if a function name follows constructor naming patterns
/// These names are implicitly treated as static methods
fn is_constructor_name(name: &str) -> bool {
    // Note: Removed `with_*` from auto-static detection because it's commonly used
    // for builder pattern methods like `with_note()` that need `self`.
    // Only `from_*` remains as a factory method pattern (e.g., `from_string`).
    matches!(name, "new" | "create" | "default" | "init") || name.starts_with("from_")
}

impl<'a> Parser<'a> {
    // === Trait ===

    pub(crate) fn parse_trait(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Trait)?;
        let name = self.expect_identifier()?;
        let generic_params = self.parse_generic_params_as_strings()?;

        // Parse super traits (trait inheritance): trait Copy: Clone
        // Need to distinguish between:
        //   trait Copy:        (no super traits, : starts body)
        //   trait Copy: Clone: (has super trait Clone, second : starts body)
        let mut super_traits = Vec::new();
        if self.check(&TokenKind::Colon) {
            // Peek ahead: if the token after : is an identifier, it's super trait syntax
            // Otherwise, the : starts the trait body
            let colon_span = self.current.span.clone();
            self.advance(); // consume ':' to peek at next token

            if matches!(self.current.kind, TokenKind::Identifier { .. }) {
                // This is super trait syntax - parse super traits as full types
                // Supports both simple traits and generic traits:
                //   trait Copy: Clone:             (simple)
                //   trait Sequence<T>: Collection<T>:  (generic)
                super_traits.push(self.parse_type()?);

                // Parse additional super traits with + separator: trait T: A + B<T>
                while self.check(&TokenKind::Plus) {
                    self.advance(); // consume '+'
                    super_traits.push(self.parse_type()?);
                }
                // After super traits, expect another : for the body
                // (which will be consumed by parse_indented_trait_body)
            } else {
                // Not super trait syntax - put the colon back for the body parser
                use crate::token::Token;
                let colon_token = Token::new(TokenKind::Colon, colon_span, ":".to_string());
                self.pending_tokens.push_front(self.current.clone());
                self.current = colon_token;
            }
        }

        let where_clause = self.parse_where_clause()?;

        let (associated_types, methods) = self.parse_indented_trait_body()?;

        Ok(Node::Trait(TraitDef {
            span: self.make_span(start_span),
            name,
            generic_params: generic_params.clone(),
            super_traits,
            where_clause,
            associated_types,
            methods,
            visibility: Visibility::Private,
            doc_comment: None,
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
        }))
    }

    // === Impl ===

    pub(crate) fn parse_impl(&mut self) -> Result<Node, ParseError> {
        self.parse_impl_with_attrs(Vec::new())
    }

    pub(crate) fn parse_impl_with_attrs(&mut self, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Impl)?;

        // Parse optional generic params for impl block: impl<T> Trait for Type<T>
        let generic_params = self.parse_generic_params_as_strings()?;

        // Parse the first type (could be trait name or target type)
        let first_type = self.parse_type()?;

        let (trait_name, trait_type_params, target_type) = if self.check(&TokenKind::For) {
            // impl Trait for Type pattern
            self.advance();
            let target = self.parse_type()?;
            // Extract simple name from first_type for trait_name
            let (trait_name_str, trait_type_params) = match &first_type {
                Type::Simple(name) => (name.clone(), vec![]),
                Type::Generic { name, args } => (name.clone(), args.clone()),
                _ => {
                    return Err(ParseError::unexpected_token(
                        "simple trait name",
                        format!("{:?}", first_type),
                        self.current.span,
                    ))
                }
            };
            (Some(trait_name_str), trait_type_params, target)
        } else {
            // impl Type pattern (inherent impl)
            (None, vec![], first_type)
        };

        let where_clause = self.parse_where_clause()?;
        let (associated_types, methods) = self.parse_indented_impl_body()?;

        Ok(Node::Impl(ImplBlock {
            span: self.make_span(start_span),
            attributes,
            generic_params,
            target_type,
            trait_name,
            trait_type_params,
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
    /// Supports empty impl blocks: `impl Trait for Type:` with no body
    pub(crate) fn parse_indented_impl_body(
        &mut self,
    ) -> Result<(Vec<AssociatedTypeImpl>, Vec<FunctionDef>), ParseError> {
        self.debug_enter("parse_indented_impl_body");

        // Expect colon
        self.expect(&TokenKind::Colon)?;

        // Check for newline (required)
        if !self.check(&TokenKind::Newline) {
            return Err(ParseError::unexpected_token(
                "Newline after impl block colon",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }
        self.advance(); // consume newline

        // Check for indent - if no indent, this is an empty impl block
        if !self.check(&TokenKind::Indent) {
            // Empty impl block is valid (for marker traits or traits with default impls)
            self.debug_exit("parse_indented_impl_body (empty)");
            return Ok((Vec::new(), Vec::new()));
        }
        self.advance(); // consume indent

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
            // Skip standalone docstrings (impl-level documentation)
            // These are docstrings that appear before any method and aren't attached to a method
            if matches!(&self.current.kind, TokenKind::String(_) | TokenKind::FString(_)) {
                self.advance(); // consume the docstring
                self.skip_newlines();
                continue;
            }
            // Skip pass/pass_dn/pass_do_nothing in impl body
            if self.check(&TokenKind::Pass) {
                self.advance();
                self.skip_newlines();
                continue;
            }
            if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "pass_dn" || name == "pass_do_nothing" || name == "pass_todo") {
                self.advance();
                self.skip_newlines();
                continue;
            }
            // Check for associated type impl: `type Item = i64`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_impl()?);
            } else {
                // Handle optional decorators (@pure, @inline, etc.)
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    decorators.push(self.parse_decorator()?);
                    self.skip_newlines();
                }
                // Handle optional `pub` visibility prefix for methods
                let visibility = if self.check(&TokenKind::Pub) {
                    self.advance();
                    crate::ast::Visibility::Public
                } else {
                    crate::ast::Visibility::Private
                };
                // Handle optional `static` keyword for static methods
                let mut is_static = if self.check(&TokenKind::Static) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Deprecated `var fn` syntax - emit warning and parse as mutable method
                let is_var_fn = if self.check(&TokenKind::Var) && self.peek_is(&TokenKind::Fn) {
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
                    // Mark as mutable if using deprecated 'var fn' syntax
                    if is_var_fn {
                        f.is_me_method = true;
                    }
                    // Add parsed decorators to the function
                    f.decorators.extend(decorators);

                    // Implicit static: constructor-like names are automatically static
                    // unless explicitly marked with 'static' (which was already handled above)
                    // BUT: `me` methods (mutable methods) are never static, even if they have constructor names
                    if !is_static && !f.is_me_method && is_constructor_name(&f.name) {
                        is_static = true;
                    }

                    // Set the is_static flag on the function
                    f.is_static = is_static;

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
                            variadic: false,
                            call_site_label: None,
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
            // Skip standalone docstrings (trait-level documentation)
            // These are docstrings that appear before any method and aren't attached to a method
            if let TokenKind::String(_) = &self.current.kind {
                self.advance(); // consume the docstring
                self.skip_newlines();
                continue;
            }
            // Skip pass/pass_dn/pass_do_nothing in trait body
            if self.check(&TokenKind::Pass) {
                self.advance();
                self.skip_newlines();
                continue;
            }
            if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "pass_dn" || name == "pass_do_nothing" || name == "pass_todo") {
                self.advance();
                self.skip_newlines();
                continue;
            }
            // Check for associated type: `type Name` or `type Name: Bound` or `type Name = Default`
            if self.check(&TokenKind::Type) {
                associated_types.push(self.parse_associated_type_def()?);
            } else {
                // Handle optional decorators (@deprecated, etc.)
                let mut decorators = Vec::new();
                while self.check(&TokenKind::At) {
                    decorators.push(self.parse_decorator()?);
                    self.skip_newlines();
                }
                // Handle async methods in trait blocks
                let is_async = self.check(&TokenKind::Async);
                if is_async {
                    self.advance();
                }
                // Handle static methods in trait blocks
                let is_static = self.check(&TokenKind::Static);
                if is_static {
                    self.advance();
                }
                // Handle 'me' (mutable method) keyword before fn
                let is_me = self.check(&TokenKind::Me);
                if is_me {
                    self.advance();
                    // Optionally consume 'fn' after 'me'
                    if self.check(&TokenKind::Fn) {
                        self.advance();
                    }
                }
                let mut method = if is_me {
                    // Parse as trait method but without expecting 'fn' token
                    self.parse_trait_method_after_fn()?
                } else {
                    self.parse_trait_method()?
                };
                method.decorators = decorators;
                method.is_static = is_static;
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

        // Parse optional bounds: `type Item: Clone + Default` or `type Iter: Iterator<Item=T>`
        let bounds = if self.check(&TokenKind::Colon) {
            self.advance();
            let mut bounds = Vec::new();

            // Parse first bound
            let bound_name = self.expect_identifier()?;

            // Check for generic arguments in bound: Iterator<Item=T>
            // Skip the generic args to avoid complexity - just store the trait name
            if self.check(&TokenKind::Lt) {
                let mut depth = 1;
                self.advance(); // consume '<'
                while depth > 0 && !self.is_at_end() {
                    if self.check(&TokenKind::Lt) {
                        depth += 1;
                        self.advance();
                    } else if self.check(&TokenKind::Gt) {
                        depth -= 1;
                        self.advance();
                    } else if self.check(&TokenKind::ShiftRight) {
                        // >> is two > tokens
                        if depth <= 2 {
                            depth -= 2;
                            self.advance();
                        } else {
                            depth -= 2;
                            self.advance();
                        }
                    } else {
                        self.advance();
                    }
                }
            }

            bounds.push(bound_name);

            // Parse additional bounds with + separator
            while self.check(&TokenKind::Plus) {
                self.advance();
                let bound_name = self.expect_identifier()?;

                // Skip generic args for additional bounds too
                if self.check(&TokenKind::Lt) {
                    let mut depth = 1;
                    self.advance();
                    while depth > 0 && !self.is_at_end() {
                        if self.check(&TokenKind::Lt) {
                            depth += 1;
                            self.advance();
                        } else if self.check(&TokenKind::Gt) {
                            depth -= 1;
                            self.advance();
                        } else if self.check(&TokenKind::ShiftRight) {
                            if depth <= 2 {
                                depth -= 2;
                                self.advance();
                            } else {
                                depth -= 2;
                                self.advance();
                            }
                        } else {
                            self.advance();
                        }
                    }
                }

                bounds.push(bound_name);
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
        self.expect(&TokenKind::Fn)?;
        self.parse_trait_method_after_fn()
    }

    fn parse_trait_method_after_fn(&mut self) -> Result<FunctionDef, ParseError> {
        let start_span = self.current.span;

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
        let (body, is_abstract) = if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) {
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
            generic_params: generic_params.clone(),
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
            is_static: false,
            is_me_method: false,
            is_generator: false,
            bounds_block: None,
            return_constraint: None,
            is_generic_template: !generic_params.is_empty(),
            specialization_of: None,
            type_bindings: HashMap::new(),
        })
    }
}
