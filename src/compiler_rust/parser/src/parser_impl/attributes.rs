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
    "modes",
    "skip_modes",
    "only_modes",
    "mode_failure_strategy",
    // Module/compiler directives
    "inline",
    "always_inline",
    "force_inline",
    "gc",
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
    "global",
    "export",
    // Driver framework (FR-DRIVER-0001): @driver(...) / @native_lib(...)
    // routed through the attribute (not decorator) path so named args like
    // `class = DriverClass.Block, vendor = ..., device = [...], version = "..."`
    // are stored on the owning declaration for FR-DRIVER-0004 to consume.
    "driver",
    "native_lib",
    // SIMD/GPU optimization requirements (Phase 1 implementation)
    "must",
    "prefer",
    "collection_algorithm",
    "error_not",
    "warn_not",
];

/// Check if a name is a known attribute (should produce Attribute, not Decorator)
pub fn is_known_attribute_name(name: &str) -> bool {
    KNOWN_ATTRIBUTE_NAMES.contains(&name)
}

impl<'a> Parser<'a> {
    pub(crate) fn collection_owner_push(&mut self, name: &str) -> String {
        let previous = self.collection_owner.clone();
        self.collection_owner = if previous.is_empty() {
            name.to_string()
        } else {
            format!("{previous}/{name}")
        };
        previous
    }

    pub(crate) fn collection_site_id(&mut self, name: &str, declaration: Span, field: bool) -> String {
        // FNV-1a is the hash_text ABI used by the self-hosted parser. Hash the
        // declaration without its attribute so a policy switch reuses feedback.
        let text = self.source.get(declaration.start..declaration.end).unwrap_or("");
        let hash = text.bytes().fold(0xcbf29ce484222325_u64, |value, byte| {
            (value ^ u64::from(byte)).wrapping_mul(0x100000001b3)
        }) as i64;
        let module = if self.collection_module_path.is_empty() {
            "<unknown>".to_string()
        } else {
            self.collection_module_path.replace(';', "_").replace('\n', "_").replace('\r', "_")
        };
        let owner = &self.collection_owner;
        let stem = if field {
            format!("ast://{module}/{owner}/{name}#{hash}")
        } else if owner.is_empty() {
            format!("ast://{module}/local/{name}#{hash}")
        } else {
            format!("ast://{module}/{owner}/local/{name}#{hash}")
        };
        if field {
            return stem;
        }
        let ordinal = self.collection_site_ordinals.entry(stem.clone()).or_insert(0);
        let site = if *ordinal == 0 { stem.clone() } else { format!("{stem}:{ordinal}") };
        *ordinal += 1;
        site
    }

    pub(crate) fn is_at_collection_algorithm(&mut self) -> bool {
        self.check(&TokenKind::At)
            && matches!(&self.peek_next().kind, TokenKind::Identifier { name, .. } if name == "collection_algorithm")
    }

    pub(crate) fn collection_algorithm_attribute(
        &self,
        attributes: &[Attribute],
    ) -> Result<Option<String>, ParseError> {
        let mut algorithm = None;
        for attribute in attributes {
            if attribute.name != "collection_algorithm" {
                continue;
            }
            if algorithm.is_some() {
                return Err(ParseError::contextual_error(
                    "collection algorithm",
                    "duplicate @collection_algorithm on one declaration",
                    attribute.span,
                ));
            }
            let name = match (&attribute.args, &attribute.named_args) {
                (Some(args), None) if args.len() == 1 => match &args[0] {
                    Expr::String(name) => name.as_str(),
                    Expr::FString { parts, .. } => match parts.as_slice() {
                        [FStringPart::Literal(name)] => name.as_str(),
                        _ => {
                            return Err(ParseError::contextual_error(
                                "collection algorithm",
                                "@collection_algorithm requires one literal string algorithm name",
                                attribute.span,
                            ));
                        }
                    },
                    _ => {
                        return Err(ParseError::contextual_error(
                            "collection algorithm",
                            "@collection_algorithm requires one string algorithm name",
                            attribute.span,
                        ));
                    }
                },
                _ => {
                    return Err(ParseError::contextual_error(
                        "collection algorithm",
                        "@collection_algorithm requires one string algorithm name",
                        attribute.span,
                    ));
                }
            };
            if !matches!(name, "auto" | "linear" | "hash" | "ordered") {
                return Err(ParseError::contextual_error(
                    "collection algorithm",
                    format!("unknown collection algorithm: {name}"),
                    attribute.span,
                ));
            }
            algorithm = Some(name.to_string());
        }
        Ok(algorithm)
    }

    pub(crate) fn collection_attributed_value(
        &self,
        value: Expr,
        algorithm: &str,
        site_id: &str,
        span: Span,
        declared_type: Option<&Type>,
    ) -> Result<Expr, ParseError> {
        let (receiver, constructor) = match &value {
            Expr::MethodCall { receiver, method, .. } => (receiver.as_ref(), method.as_str()),
            Expr::Call { callee, .. } => match callee.as_ref() {
                Expr::FieldAccess { receiver, field } => (receiver.as_ref(), field.as_str()),
                _ => (&value, ""),
            },
            _ => (&value, ""),
        };
        let receiver_family = match receiver {
            Expr::Identifier(name) if matches!(name.as_str(), "AdaptiveTextSet" | "AdaptiveTextMap" | "AdaptiveSet" | "AdaptiveMap") => Some(name.as_str()),
            _ => None,
        };
        let declared_family = match declared_type {
            Some(Type::Simple(name) | Type::Generic { name, .. })
                if matches!(name.as_str(), "AdaptiveTextSet" | "AdaptiveTextMap" | "AdaptiveSet" | "AdaptiveMap") => Some(name.as_str()),
            _ => None,
        };
        let common_constructor = matches!(constructor, "new" | "with_profile" | "with_site_and_target");
        let text_constructor = matches!(constructor, "with_site" | "with_attribute")
            && matches!(receiver_family, Some("AdaptiveTextSet" | "AdaptiveTextMap"));
        let direct_family = if common_constructor || text_constructor { receiver_family } else { None };
        if receiver_family.is_some() && direct_family.is_none() && declared_family != receiver_family {
            return Err(ParseError::contextual_error(
                "collection algorithm",
                "@collection_algorithm requires a written adaptive family for this method",
                span,
            ));
        }
        if direct_family.is_some() && declared_family.is_some() && direct_family != declared_family {
            return Err(ParseError::contextual_error(
                "collection algorithm",
                "@collection_algorithm constructor conflicts with the written adaptive family",
                span,
            ));
        }
        let family = direct_family.or(declared_family).ok_or_else(|| ParseError::contextual_error(
            "collection algorithm",
            "@collection_algorithm requires an adaptive set or map initializer with a known family",
            span,
        ))?;
        let effective_site = if direct_family.is_some() && matches!(constructor, "with_site" | "with_site_and_target" | "with_attribute") {
            let args = match &value {
                Expr::MethodCall { args, .. } | Expr::Call { args, .. } => args,
                _ => unreachable!("validated collection constructor is a call"),
            };
            let literal_site = match args.get(1).map(|argument| &argument.value) {
                Some(Expr::String(explicit)) => Some(explicit.as_str()),
                Some(Expr::FString { parts, .. }) if parts.len() == 1 => match &parts[0] {
                    FStringPart::Literal(explicit) => Some(explicit.as_str()),
                    _ => None,
                },
                _ => None,
            };
            match literal_site {
                Some(explicit) if explicit.starts_with("ast://") => explicit.to_string(),
                Some(_) => {
                    return Err(ParseError::contextual_error(
                        "collection algorithm",
                        "@collection_algorithm requires an ast:// explicit site",
                        span,
                    ));
                }
                _ => {
                    return Err(ParseError::contextual_error(
                        "collection algorithm",
                        "@collection_algorithm requires a literal ast:// explicit site",
                        span,
                    ));
                }
            }
        } else {
            site_id.to_string()
        };
        Ok(Expr::MethodCall {
            receiver: Box::new(Expr::Identifier(family.to_string())),
            method: "attributed_at_site".to_string(),
            args: vec![
                Argument::with_span(None, value, span),
                Argument::with_span(None, Expr::String(algorithm.to_string()), span),
                Argument::with_span(None, Expr::String(effective_site), span),
            ],
            generic_args: Vec::new(),
        })
    }

    /// Check if current token is @ followed by a known attribute name.
    /// Used to distinguish lint-style attributes from effect decorators such as
    /// `@async`.
    pub(crate) fn is_at_known_attribute(&mut self) -> bool {
        if !self.check(&TokenKind::At) {
            return false;
        }
        let next = self.peek_next();
        match &next.kind {
            TokenKind::Identifier { name, .. } => is_known_attribute_name(name),
            TokenKind::Allow => true,
            TokenKind::Default => true,
            TokenKind::Extern => true,
            TokenKind::Export => true,
            _ => false,
        }
    }

    /// Parse a single attribute: #[name] or #[name = value] or #[name(args)]
    /// DEPRECATED: This method parses the legacy #[...] syntax. All attributes should
    /// use @name(args) syntax instead. This method is retained for reference but is no
    /// longer called from the main parsing pipeline.
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
        // appear as decorator names in lint-level and policy decorators.
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
