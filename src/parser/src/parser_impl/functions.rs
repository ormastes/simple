//! Function parsing
//!
//! This module handles parsing of function definitions, including decorators,
//! attributes, doc comments, and contract blocks.

use crate::ast::*;
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
        }
        Ok(func)
    }

    pub(crate) fn parse_function(&mut self) -> Result<Node, ParseError> {
        self.parse_function_with_decorators(vec![])
    }

    pub(super) fn parse_function_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        self.parse_function_with_attrs(decorators, vec![])
    }

    pub(super) fn parse_function_with_attrs(
        &mut self,
        decorators: Vec<Decorator>,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Fn)?;

        // Allow keywords like 'new', 'type', etc. as function names
        let name = self.expect_method_name()?;
        // Parse optional generic parameters: fn foo<T, U>(...)
        let generic_params = self.parse_generic_params_as_strings()?;
        let params = self.parse_parameters()?;

        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Parse optional where clause: where T: Clone + Default
        let where_clause = self.parse_where_clause()?;

        // Skip newlines before the function body colon or abstract semicolon
        self.skip_newlines();

        // Check for abstract method (semicolon instead of body)
        let is_abstract = if self.check(&TokenKind::Semicolon) {
            self.advance();
            true
        } else {
            false
        };

        let (body, contract, bounds_block) = if is_abstract {
            // Abstract method has no body
            let empty_span = Span::new(start_span.start, start_span.end, start_span.line, start_span.column);
            (Block { span: empty_span, statements: vec![] }, None, None)
        } else {
            self.expect(&TokenKind::Colon)?;

            // After the colon, expect NEWLINE + INDENT to start the function body
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

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
            let has_simd = decorators.iter().any(|d| {
                matches!(&d.name, Expr::Identifier(name) if name == "simd")
            });

            let bounds_block = if has_simd {
                // Skip newlines after body to check for bounds:
                self.skip_newlines();
                self.parse_bounds_block()?
            } else {
                None
            };

            (body, contract, bounds_block)
        };

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
            where_clause,
            body,
            visibility: Visibility::Private,
            effects: vec![],
            decorators,
            attributes,
            doc_comment: None,
            contract,
            is_abstract,
            is_sync: false,
            bounds_block,
        }))
    }

    /// Parse optional where clause: `where T: Trait1 + Trait2, U: Other`
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

            // Parse trait bounds: Trait1 + Trait2 + ...
            let mut trait_bounds = Vec::new();
            loop {
                let bound_name = self.expect_identifier()?;
                trait_bounds.push(bound_name);

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
                negative_bounds: vec![], // TODO: [parser][P2] Parse !Trait syntax (#1151)
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

    pub(super) fn parse_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
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

    pub(super) fn parse_sync_function_with_doc(
        &mut self,
        doc_comment: Option<DocComment>,
    ) -> Result<Node, ParseError> {
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

    /// Parse a decorated function: @decorator fn foo(): ...
    /// Effect decorators (@pure, @io, @net, @fs, @unsafe, @async) are extracted
    /// into the function's effects field; other decorators remain in decorators field.
    pub(super) fn parse_decorated_function(&mut self) -> Result<Node, ParseError> {
        let mut decorators = Vec::new();
        let mut effects = Vec::new();

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
                    continue;
                }
            }

            // Not an effect decorator - keep as regular decorator
            decorators.push(decorator);

            // Skip newlines between decorators
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
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
