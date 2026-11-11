//! Type definition parsing
//!
//! This module handles parsing of struct, class, enum, union, and trait definitions
//! with doc comments, as well as alias definitions.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

impl<'a> Parser<'a> {
    pub(super) fn parse_struct_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_struct()?;
        if let Node::Struct(ref mut s) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            s.doc_comment = doc_comment.or(s.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_class_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_class()?;
        if let Node::Class(ref mut c) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            c.doc_comment = doc_comment.or(c.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_enum_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_enum()?;
        if let Node::Enum(ref mut e) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            e.doc_comment = doc_comment.or(e.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_union_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_union()?;
        if let Node::Enum(ref mut e) = node {
            // Prefer leading doc comment, fall back to inline docstring from body
            e.doc_comment = doc_comment.or(e.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_trait_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_trait()?;
        if let Node::Trait(ref mut t) = node {
            t.doc_comment = doc_comment;
        }
        Ok(node)
    }

    pub(super) fn parse_mixin_with_doc(&mut self, doc_comment: Option<DocComment>) -> Result<Node, ParseError> {
        let mut node = self.parse_mixin()?;
        if let Node::Mixin(ref mut m) = node {
            m.doc_comment = doc_comment.or(m.doc_comment.take());
        }
        Ok(node)
    }

    pub(super) fn parse_mixin_with_attrs(&mut self, _attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        self.parse_mixin()
    }

    pub(super) fn parse_trait_with_attrs(&mut self, _attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        self.parse_trait()
    }

    /// Parse a class/struct/enum alias: `alias NewName = OldName`
    ///
    /// # Syntax
    /// ```simple
    /// alias Point2D = Point
    /// alias Optional = Option
    ///
    /// @deprecated("Use Point2D instead")
    /// alias OldPoint = Point
    /// ```
    pub(crate) fn parse_class_alias(&mut self) -> Result<Node, ParseError> {
        self.parse_class_alias_with_decorators(vec![])
    }

    /// Parse a class alias with decorators
    pub(crate) fn parse_class_alias_with_decorators(&mut self, decorators: Vec<Decorator>) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Alias)?;

        // Expect the new alias name (PascalCase identifier)
        let name = self.expect_identifier()?;

        self.expect(&TokenKind::Assign)?;

        // Expect the target type name
        let target = self.expect_identifier()?;

        Ok(Node::ClassAlias(ClassAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            target,
            visibility: Visibility::Private,
            decorators,
            doc_comment: None,
        }))
    }

    /// Parse a function alias: `fn new_name = old_name`
    ///
    /// This is called when we detect the pattern `fn name = target` instead of
    /// `fn name(...)`. The detection happens in parse_function_with_attrs.
    ///
    /// # Syntax
    /// ```simple
    /// fn println = print
    ///
    /// @deprecated("Use println instead")
    /// fn old_print = print
    /// ```
    pub(crate) fn parse_function_alias(&mut self) -> Result<Node, ParseError> {
        self.parse_function_alias_with_decorators(vec![])
    }

    /// Parse a function alias with decorators
    pub(crate) fn parse_function_alias_with_decorators(
        &mut self,
        decorators: Vec<Decorator>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        self.expect(&TokenKind::Fn)?;

        // Expect the new alias name
        let name = self.expect_identifier()?;

        self.expect(&TokenKind::Assign)?;

        // Expect the target function name
        let target = self.expect_identifier()?;

        Ok(Node::FunctionAlias(FunctionAliasDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            target,
            visibility: Visibility::Private,
            decorators,
            doc_comment: None,
        }))
    }

    /// `@sffi(prefix: "...", ...) resource Name` (Grammar A). Mirrors the
    /// pure-Simple `parse_resource_decl` (10.frontend enum_module_body.spl):
    /// `@sffi` with a `prefix:` key is required, unknown keys are rejected,
    /// and the decl only registers `Name` as a type. It lowers to an empty,
    /// method-less struct carrying the `sffi` metadata as named args.
    pub(crate) fn parse_resource_decl(
        &mut self,
        decorators: Vec<Decorator>,
        visibility: Visibility,
    ) -> Result<Node, ParseError> {
        const SFFI_KEYS: [&str; 7] = ["prefix", "handle", "invalid", "retain", "release", "sharing", "thread_safe"];
        let start_span = self.current.span;
        self.advance(); // soft keyword `resource`
        let name = self.expect_identifier()?;
        let mut sffi: Option<Vec<(String, Expr)>> = None;
        for decorator in decorators {
            let is_sffi = matches!(&decorator.name, Expr::Identifier(n) if n == "sffi");
            if !is_sffi {
                return Err(ParseError::syntax_error_with_span(
                    format!("unsupported decorator on `resource {name}`; only `@sffi(...)` is allowed"),
                    decorator.span,
                ));
            }
            let mut named = Vec::new();
            for arg in decorator.args.unwrap_or_default() {
                let Some(key) = arg.name else {
                    return Err(ParseError::syntax_error_with_span(
                        "`@sffi` arguments must be named (`key: value`)",
                        arg.span,
                    ));
                };
                if !SFFI_KEYS.contains(&key.as_str()) {
                    return Err(ParseError::syntax_error_with_span(
                        format!("unknown `@sffi` key `{key}`; expected one of prefix, handle, invalid, retain, release, sharing, thread_safe"),
                        arg.span,
                    ));
                }
                named.push((key, arg.value));
            }
            sffi = Some(named);
        }
        let Some(named) = sffi else {
            return Err(ParseError::syntax_error_with_span(
                format!("`resource {name}` requires an `@sffi(prefix: \"...\")` attribute"),
                start_span,
            ));
        };
        if !named.iter().any(|(k, _)| k == "prefix") {
            return Err(ParseError::syntax_error_with_span(
                format!("`@sffi` on `resource {name}` is missing the required `prefix:` key"),
                start_span,
            ));
        }
        Ok(Node::Struct(StructDef {
            span: start_span,
            name,
            generic_params: Vec::new(),
            where_clause: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            visibility,
            attributes: vec![Attribute {
                span: start_span,
                name: "sffi".to_string(),
                value: None,
                args: None,
                named_args: Some(named),
            }],
            doc_comment: None,
            invariant: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: Default::default(),
        }))
    }
}
