//! Attribute and decorator parsing
//!
//! This module handles parsing of attributes (@name and legacy #[...]) and decorators (@...).
//! New code should prefer @name attributes, but #[...] remains accepted for compatibility.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::core::Parser;

/// Known attribute names that should be parsed as Attribute (not Decorator) when using @ syntax.
/// These are non-effect, non-decorator tags used for metadata, lint control, test config, etc.
pub const KNOWN_ATTRIBUTE_NAMES: &[&str] = &[
    // Lint control
    "allow",
    "warn",
    "deny",
    // Test/spec metadata
    "timeout",
    "tag",
    "skip",
    "ignore",
    "only",
    "slow",
    "flaky",
    "test",
    "modes",
    "skip_modes",
    "only_modes",
    "mode_failure_strategy",
    // Module/compiler directives
    "inline",
    "bypass",
    "no_gc",
    "no_prelude",
    "no_auto_defer",
    "no_mangle",
    "default",
    "derive",
    "repr",
    "packed",
    "cfg",
    // Layout/memory
    "layout",
    "variant",
    "id",
    "no_alloc",
    "alloc",
    "immutable",
    // Misc
    "retry",
    "ratelimit",
    "gpu",
    "gpu_kernel",
    "distributed",
    "cache",
    "mock",
    "deprecated",
    "config",
    "extern",
    "async",
    "unsafe",
    "concurrency_mode",
    "no_auto_defer",
    // SimpleOS / codegen
    "entry",
    "noreturn",
    "naked",
    "section",
    "interrupt",
    "boot",
    "align",
    "export",
    // Driver framework (FR-DRIVER-0001): @driver(...) / @native_lib(...)
    // routed through the attribute (not decorator) path so named args like
    // `class = DriverClass.Block, vendor = ..., device = [...], version = "..."`
    // are stored on the owning declaration for FR-DRIVER-0004 to consume.
    "driver",
    "native_lib",
];

/// Check if a name is a known attribute (should produce Attribute, not Decorator)
pub fn is_known_attribute_name(name: &str) -> bool {
    KNOWN_ATTRIBUTE_NAMES.contains(&name)
}

impl<'a> Parser<'a> {
    /// Check if current token is @ followed by a known attribute name.
    /// Used to distinguish @allow(lint) (attribute) from @async (effect decorator).
    pub(crate) fn is_at_known_attribute(&mut self) -> bool {
        if !self.check(&TokenKind::At) {
            return false;
        }
        let next = self.peek_next();
        match &next.kind {
            TokenKind::Identifier { name, .. } => is_known_attribute_name(name),
            TokenKind::Allow => true,
            TokenKind::Default => true,
            TokenKind::Async => true,
            TokenKind::Extern => true,
            TokenKind::Export => true,
            _ => false,
        }
    }

    /// Parse a single attribute: #[name] or #[name = value] or #[name(args)]
    /// DEPRECATED: This method parses the legacy #[...] syntax. All attributes should
    /// use @name(args) syntax instead. This method is retained for reference but is no
    /// longer called from the main parsing pipeline.
    #[allow(dead_code)]
    pub(crate) fn parse_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Hash)?;
        self.expect(&TokenKind::LBracket)?;

        // Parse the attribute name - accept identifiers and some keywords
        let name = match &self.current.kind {
            TokenKind::Identifier { name: s, .. } => {
                let name = s.clone();
                self.advance();
                name
            }
            // Accept keywords that can be used as attribute names
            TokenKind::Allow => {
                self.advance();
                "allow".to_string()
            }
            TokenKind::Default => {
                self.advance();
                "default".to_string()
            }
            _ => {
                return Err(ParseError::unexpected_token(
                    "identifier or attribute keyword",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };

        // Check for value: #[name = value]
        let value = if self.check(&TokenKind::Assign) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        // Check for arguments: #[name(arg1, arg2)]
        let args = self.parse_optional_paren_args()?;

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
            named_args: None,
        })
    }

    /// Parse a single decorator: @name or @name(args)
    /// Also handles @async which uses a keyword instead of identifier.
    /// Supports named arguments: @bounds(default="return", strict=true)
    pub(crate) fn parse_decorator(&mut self) -> Result<Decorator, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Handle keywords specially since they can be decorator names.
        // Allow/Warn/Deny/Forbid are also keywords (used in arch rules) but can
        // appear as decorator names in @allow(...), @warn(...), etc.
        let expr = if self.check(&TokenKind::Async) {
            self.advance();
            Expr::Identifier("async".to_string())
        } else if self.check(&TokenKind::Bounds) {
            self.advance();
            Expr::Identifier("bounds".to_string())
        } else if self.check(&TokenKind::Extern) {
            self.advance();
            Expr::Identifier("extern".to_string())
        } else if self.check(&TokenKind::Allow) {
            self.advance();
            Expr::Identifier("allow".to_string())
        } else if self.check(&TokenKind::Forbid) {
            self.advance();
            Expr::Identifier("forbid".to_string())
        } else if self.check(&TokenKind::Default) {
            self.advance();
            Expr::Identifier("default".to_string())
        } else {
            // Parse the decorator expression (can be dotted/called: @module.decorator or @trainer.on(Events.X))
            self.parse_postfix()?
        };

        // If the expression is a Call, extract the callee as name and arguments
        // This handles both @decorator(args) and @obj.method(args)
        let (name, args) = match expr {
            Expr::Call {
                callee,
                args: call_args,
            } => {
                // Convert Argument to the decorator's args format
                (*callee, Some(call_args))
            }
            other => {
                // Check for additional arguments after a non-call expression
                // This handles the rare case of @decorator followed by separate args
                let args = if self.check(&TokenKind::LParen) {
                    Some(self.parse_arguments()?)
                } else {
                    None
                };
                (other, args)
            }
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

    /// Parse @name or @name(args) as an Attribute (not Decorator).
    /// Used when @ is followed by a known attribute name.
    pub(crate) fn parse_at_as_attribute(&mut self) -> Result<Attribute, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::At)?;

        // Parse the attribute name
        let name = match &self.current.kind {
            TokenKind::Identifier { name: s, .. } => {
                let name = s.clone();
                self.advance();
                name
            }
            TokenKind::Allow => {
                self.advance();
                "allow".to_string()
            }
            TokenKind::Default => {
                self.advance();
                "default".to_string()
            }
            TokenKind::Async => {
                self.advance();
                "async".to_string()
            }
            TokenKind::Extern => {
                self.advance();
                "extern".to_string()
            }
            TokenKind::Export => {
                self.advance();
                "export".to_string()
            }
            _ => {
                return Err(ParseError::unexpected_token(
                    "attribute name",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };

        // Check for arguments: @name(arg1, arg2) OR @name(key = value, ...).
        //
        // FR-DRIVER-0004: parse via `parse_arguments()` (not the flat
        // `parse_optional_paren_args`) so named arguments like
        // `@driver(dclass = DriverClass.Block, vendor = 0x8086, ...)`
        // survive parse with their names intact. `parse_arguments` already
        // accepts keywords (`class`, `default`, ...) as named-arg keys.
        //
        // The typed `name = value` pairs land on `Attribute.named_args`;
        // the `args` field keeps a flat `Vec<Expr>` (positional-first,
        // then named-as-Identifier-placeholders) for backward-compat with
        // pre-FR-0004 consumers that still expect raw `Expr`.
        let (args, named_args) = if self.check(&TokenKind::LParen) {
            let arguments = self.parse_arguments()?;
            let mut positional: Vec<crate::ast::Expr> = Vec::new();
            let mut named: Vec<(String, crate::ast::Expr)> = Vec::new();
            for argument in arguments {
                match argument.name {
                    Some(nm) => {
                        // Preserve the key as an Identifier in the flat
                        // `args` list so legacy Identifier-matching code
                        // still sees the name; the real value moves to
                        // `named_args`.
                        positional.push(crate::ast::Expr::Identifier(nm.clone()));
                        named.push((nm, argument.value));
                    }
                    None => positional.push(argument.value),
                }
            }
            let named_opt = if named.is_empty() { None } else { Some(named) };
            (Some(positional), named_opt)
        } else {
            (None, None)
        };

        Ok(Attribute {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            value: None,
            args,
            named_args,
        })
    }

    /// Parse optional parenthesized argument list: `(arg1, arg2, ...)`
    pub(super) fn parse_optional_paren_args(&mut self) -> Result<Option<Vec<Expr>>, ParseError> {
        if self.check(&TokenKind::LParen) {
            self.advance();
            let mut args = Vec::new();
            while !self.check(&TokenKind::RParen) {
                args.push(self.parse_expression()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            Ok(Some(args))
        } else {
            Ok(None)
        }
    }
}
