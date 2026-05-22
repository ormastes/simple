//! Parser for AOP (Aspect-Oriented Programming) statements.
//!
//! This module implements parsing for:
//! - AOP advice declarations: `on pc{...} use <Interceptor> priority N`
//! - DI bindings: `bind on pc{...} -> <Impl> scope priority`
//! - Architecture rules: `forbid pc{...}`, `allow pc{...}`
//! - Mock declarations: `mock Name implements Trait:`
//!
//! See doc/research/aop.md for the complete specification.

use crate::ast::{
    AdviceType, AopAdvice, ArchRuleType, ArchitectureRule, CapabilityItem, CapabilityPolicy, DiBinding, DiScope,
    InjectGraph, InjectItem, InjectLifetime, InjectMode, MockDecl, PredicateExpr, SandboxItem, SandboxPolicy,
    SecurityGate, SecurityItem, SecurityPolicy,
};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    /// Parse an AOP advice declaration: `on pc{...} use <Interceptor>`
    ///
    /// Full syntax:
    /// ```simple
    /// on pc{ execution(* User.new(..)) } use LoggingInterceptor priority 10
    /// ```
    pub fn parse_aop_advice(&mut self) -> Result<AopAdvice, ParseError> {
        let start = self.current.span;

        // Expect 'on'
        self.expect(&TokenKind::On)?;

        // Parse pointcut predicate
        let pointcut = self.parse_pointcut()?;

        // Expect 'use'
        self.expect(&TokenKind::Use)?;

        // Parse interceptor name (qualified identifier)
        let interceptor = self.expect_identifier()?;

        // Parse optional advice type (default: before)
        let advice_type = if let TokenKind::Identifier { name, .. } = &self.current.kind {
            match name.as_str() {
                "before" | "after_success" | "after_error" | "around" => {
                    let type_name = name.clone();
                    self.advance();
                    AdviceType::parse_str(&type_name).ok_or_else(|| {
                        ParseError::unexpected_token("valid advice type", type_name, self.previous.span)
                    })?
                }
                _ => AdviceType::Before, // Default
            }
        } else {
            AdviceType::Before
        };

        // Parse optional priority
        let priority = if let TokenKind::Identifier { name: s, .. } = &self.current.kind {
            if s == "priority" {
                self.advance(); // consume 'priority'
                if let TokenKind::Integer(val) = self.current.kind {
                    let v = val;
                    self.advance();
                    Some(v)
                } else {
                    return Err(ParseError::unexpected_token(
                        "integer",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
            } else {
                None
            }
        } else {
            None
        };

        let end = self.previous.span;
        Ok(AopAdvice {
            pointcut,
            advice_type,
            interceptor,
            priority,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    /// Parse a first-class DI graph declaration:
    ///
    /// ```simple
    /// inject AppGraph compile:
    ///     root App
    ///     scan app.*
    ///     bind UserRepo = SqlUserRepo lifetime scoped configurable
    ///     slot PaymentProvider runtime named payments default StripePaymentProvider
    ///     load "config/di.sdn"
    /// ```
    pub fn parse_inject_graph(&mut self) -> Result<InjectGraph, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("inject")?;
        let name = self.expect_identifier()?;

        let mode = if let TokenKind::Identifier { name, .. } = &self.current.kind {
            if let Some(mode) = InjectMode::parse_str(name) {
                self.advance();
                Some(mode)
            } else {
                None
            }
        } else {
            None
        };

        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let items = self.parse_inject_items()?;
        self.expect(&TokenKind::Dedent)?;

        let end = self.previous.span;
        Ok(InjectGraph {
            name,
            mode,
            items,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    fn parse_inject_items(&mut self) -> Result<Vec<InjectItem>, ParseError> {
        let mut items = Vec::new();
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            items.push(self.parse_inject_item()?);
            self.skip_newlines();
        }
        Ok(items)
    }

    fn parse_inject_item(&mut self) -> Result<InjectItem, ParseError> {
        match &self.current.kind {
            TokenKind::Identifier { name, .. } if name == "root" => self.parse_inject_root(),
            TokenKind::Identifier { name, .. } if name == "scan" => self.parse_inject_scan(),
            TokenKind::Identifier { name, .. } if name == "load" => self.parse_inject_load(),
            TokenKind::Identifier { name, .. } if name == "slot" => self.parse_inject_slot(),
            TokenKind::Identifier { name, .. } if name == "profile" => self.parse_inject_profile(),
            TokenKind::Bind => self.parse_inject_bind(),
            _ => Err(ParseError::unexpected_token(
                "root, scan, bind, slot, load, or profile in inject graph",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn parse_inject_root(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("root")?;
        let type_ref = self.collect_until_line_end();
        if type_ref.is_empty() {
            return Err(ParseError::unexpected_token(
                "root type",
                "end of line".to_string(),
                self.current.span,
            ));
        }
        Ok(InjectItem::Root {
            type_ref,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_scan(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("scan")?;
        let pattern = self.collect_until_line_end();
        if pattern.is_empty() {
            return Err(ParseError::unexpected_token(
                "scan path pattern",
                "end of line".to_string(),
                self.current.span,
            ));
        }
        Ok(InjectItem::Scan {
            pattern,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_load(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("load")?;
        let path = match &self.current.kind {
            TokenKind::String(path) | TokenKind::RawString(path) => {
                let path = path.clone();
                self.advance();
                path
            }
            TokenKind::FString(parts) if parts.is_empty() || parts.len() == 1 => {
                if parts.is_empty() {
                    self.advance();
                    String::new()
                } else if let crate::token::FStringToken::Literal(path) = &parts[0] {
                    let path = path.clone();
                    self.advance();
                    path
                } else {
                    return Err(ParseError::unexpected_token(
                        "static string path",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
            }
            _ => {
                return Err(ParseError::unexpected_token(
                    "string path",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        };
        self.ensure_line_end()?;
        Ok(InjectItem::Load {
            path,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_bind(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect(&TokenKind::Bind)?;
        let service = self.collect_until_token(|kind| matches!(kind, TokenKind::Assign));
        if service.is_empty() {
            return Err(ParseError::unexpected_token(
                "binding service type",
                "=".to_string(),
                self.current.span,
            ));
        }
        self.expect(&TokenKind::Assign)?;
        let target = self.collect_until_token(Self::is_inject_bind_modifier_kind);
        if target.is_empty() {
            return Err(ParseError::unexpected_token(
                "binding target type",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }

        let mut lifetime = None;
        let mut configurable = false;
        let mut final_binding = false;
        while !matches!(
            &self.current.kind,
            TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) {
            match &self.current.kind {
                TokenKind::Identifier { name, .. } if name == "lifetime" => {
                    self.advance();
                    lifetime = Some(self.parse_inject_lifetime()?);
                }
                TokenKind::Identifier { name, .. } if name == "configurable" => {
                    configurable = true;
                    self.advance();
                }
                TokenKind::Identifier { name, .. } if name == "final" => {
                    final_binding = true;
                    self.advance();
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "lifetime, configurable, final, or end of line",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        }

        Ok(InjectItem::Bind {
            service,
            target,
            lifetime,
            configurable,
            final_binding,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_slot(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("slot")?;
        let service = self.collect_until_identifier("runtime");
        if service.is_empty() {
            return Err(ParseError::unexpected_token(
                "runtime slot type",
                "runtime".to_string(),
                self.current.span,
            ));
        }
        self.expect_identifier_named("runtime")?;

        let mut qualifier = None;
        let mut default_target = None;
        while !matches!(
            &self.current.kind,
            TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) {
            match &self.current.kind {
                TokenKind::Identifier { name, .. } if name == "named" => {
                    self.advance();
                    qualifier = Some(self.expect_identifier()?);
                }
                TokenKind::Default => {
                    self.advance();
                    default_target = Some(self.collect_until_line_end());
                    break;
                }
                TokenKind::Identifier { name, .. } if name == "default" => {
                    self.advance();
                    default_target = Some(self.collect_until_line_end());
                    break;
                }
                _ => {
                    return Err(ParseError::unexpected_token(
                        "named, default, or end of line",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ))
                }
            }
        }

        Ok(InjectItem::Slot {
            service,
            qualifier,
            default_target,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_profile(&mut self) -> Result<InjectItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("profile")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let items = self.parse_inject_items()?;
        self.expect(&TokenKind::Dedent)?;
        Ok(InjectItem::Profile {
            name,
            items,
            span: self.span_from_start(start),
        })
    }

    fn parse_inject_lifetime(&mut self) -> Result<InjectLifetime, ParseError> {
        match &self.current.kind {
            TokenKind::Identifier { name, .. } => {
                let value = name.clone();
                let span = self.current.span;
                self.advance();
                InjectLifetime::parse_str(&value)
                    .ok_or_else(|| ParseError::unexpected_token("valid DI lifetime", value, span))
            }
            TokenKind::Static => {
                self.advance();
                Ok(InjectLifetime::Static)
            }
            TokenKind::Extern => {
                self.advance();
                Ok(InjectLifetime::Extern)
            }
            _ => Err(ParseError::unexpected_token(
                "DI lifetime",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn expect_identifier_named(&mut self, expected: &str) -> Result<(), ParseError> {
        match &self.current.kind {
            TokenKind::Identifier { name, .. } if name == expected => {
                self.advance();
                Ok(())
            }
            _ => Err(ParseError::unexpected_token(
                expected,
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn collect_until_line_end(&mut self) -> String {
        self.collect_until_token(|kind| matches!(kind, TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof))
    }

    fn collect_until_identifier(&mut self, expected: &str) -> String {
        self.collect_until_token(|kind| matches!(kind, TokenKind::Identifier { name, .. } if name == expected))
    }

    fn collect_until_token<F>(&mut self, stop: F) -> String
    where
        F: Fn(&TokenKind) -> bool,
    {
        let mut value = String::new();
        while !stop(&self.current.kind) {
            if matches!(
                &self.current.kind,
                TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
            ) {
                break;
            }
            value.push_str(&self.current.lexeme);
            self.advance();
        }
        value.trim().to_string()
    }

    fn ensure_line_end(&mut self) -> Result<(), ParseError> {
        if matches!(
            &self.current.kind,
            TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) {
            Ok(())
        } else {
            Err(ParseError::unexpected_token(
                "end of line",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn is_inject_bind_modifier_kind(kind: &TokenKind) -> bool {
        matches!(kind, TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof)
            || matches!(kind, TokenKind::Identifier { name, .. } if name == "lifetime" || name == "configurable" || name == "final")
    }

    fn span_from_start(&self, start: Span) -> Span {
        Span::new(start.start, self.previous.span.end, start.line, start.column)
    }

    pub fn parse_security_policy(&mut self) -> Result<SecurityPolicy, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("security")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let items = self.parse_security_items()?;
        self.expect(&TokenKind::Dedent)?;
        Ok(SecurityPolicy {
            name,
            items,
            conventions_enabled: true,
            span: self.span_from_start(start),
        })
    }

    pub fn parse_top_level_security_gate(&mut self) -> Result<SecurityGate, ParseError> {
        self.expect_identifier_named("security")?;
        self.parse_security_gate_after_keyword()
    }

    fn parse_security_items(&mut self) -> Result<Vec<SecurityItem>, ParseError> {
        let mut items = Vec::new();
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            items.push(self.parse_security_item()?);
            self.skip_newlines();
        }
        Ok(items)
    }

    fn parse_security_item(&mut self) -> Result<SecurityItem, ParseError> {
        let start = self.current.span;
        match &self.current.kind {
            TokenKind::Identifier { name, .. } if name == "root" => {
                self.advance();
                Ok(SecurityItem::Root {
                    path: self.collect_until_line_end(),
                    span: self.span_from_start(start),
                })
            }
            TokenKind::Default => {
                self.advance();
                Ok(SecurityItem::Default {
                    action: self.collect_until_line_end(),
                    span: self.span_from_start(start),
                })
            }
            TokenKind::Identifier { name, .. } if name == "default" => {
                self.advance();
                Ok(SecurityItem::Default {
                    action: self.collect_until_line_end(),
                    span: self.span_from_start(start),
                })
            }
            TokenKind::Identifier { name, .. } if name == "dimension" => self.parse_security_dimension(),
            TokenKind::Allow => self.parse_security_allow(),
            TokenKind::Identifier { name, .. } if name == "deny" => self.parse_security_deny(),
            TokenKind::Identifier { name, .. } if name == "gate" => {
                self.parse_security_gate_after_keyword().map(SecurityItem::Gate)
            }
            _ => Ok(SecurityItem::Raw {
                text: self.collect_until_line_end(),
                span: self.span_from_start(start),
            }),
        }
    }

    fn parse_security_dimension(&mut self) -> Result<SecurityItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("dimension")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let mut rules = Vec::new();
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            let rule = self.collect_security_clause_until_line_end();
            if !rule.is_empty() {
                rules.push(rule);
            }
            self.skip_newlines();
        }
        self.expect(&TokenKind::Dedent)?;
        Ok(SecurityItem::Dimension {
            name,
            rules,
            span: self.span_from_start(start),
        })
    }

    fn parse_security_allow(&mut self) -> Result<SecurityItem, ParseError> {
        let start = self.current.span;
        self.expect(&TokenKind::Allow)?;
        let from = self.collect_security_clause_until_token(|kind| matches!(kind, TokenKind::Arrow));
        self.expect(&TokenKind::Arrow)?;
        let to = self.collect_security_clause_until_identifier("through");
        let through = if matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "through") {
            self.advance();
            Some(self.collect_until_line_end())
        } else {
            None
        };
        Ok(SecurityItem::Allow {
            from,
            to,
            through,
            span: self.span_from_start(start),
        })
    }

    fn parse_security_deny(&mut self) -> Result<SecurityItem, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("deny")?;
        let from = self.collect_security_clause_until_token(|kind| matches!(kind, TokenKind::Arrow));
        self.expect(&TokenKind::Arrow)?;
        let to = self.collect_security_clause_until_token(|kind| {
            matches!(kind, TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof)
                || matches!(kind, TokenKind::Identifier { name, .. } if name == "except" || name == "direct")
        });
        let mut except = None;
        let mut direct = false;
        while !matches!(
            &self.current.kind,
            TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) {
            match &self.current.kind {
                TokenKind::Identifier { name, .. } if name == "except" => {
                    self.advance();
                    except = Some(self.collect_until_line_end());
                    break;
                }
                TokenKind::Identifier { name, .. } if name == "direct" => {
                    direct = true;
                    self.advance();
                }
                _ => self.advance(),
            }
        }
        Ok(SecurityItem::Deny {
            from,
            to,
            except,
            direct,
            span: self.span_from_start(start),
        })
    }

    fn parse_security_gate_after_keyword(&mut self) -> Result<SecurityGate, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("gate")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let mut gate = SecurityGate {
            name,
            from: None,
            to: None,
            policy: None,
            audit: None,
            sandbox: None,
            grants: Vec::new(),
            body: Vec::new(),
            span: start,
        };
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            match &self.current.kind {
                TokenKind::From => {
                    self.advance();
                    gate.from = Some(self.collect_security_clause_until_line_end());
                }
                TokenKind::To => {
                    self.advance();
                    gate.to = Some(self.collect_security_clause_until_line_end());
                }
                TokenKind::Identifier { name, .. } if name == "policy" => {
                    self.advance();
                    gate.policy = Some(self.collect_until_line_end());
                }
                TokenKind::Identifier { name, .. } if name == "audit" => {
                    self.advance();
                    gate.audit = Some(self.collect_until_line_end());
                }
                TokenKind::Identifier { name, .. } if name == "sandbox" => {
                    self.advance();
                    gate.sandbox = Some(self.collect_until_line_end());
                }
                TokenKind::Identifier { name, .. } if name == "grant" => {
                    self.advance();
                    self.expect(&TokenKind::Colon)?;
                    self.expect(&TokenKind::Newline)?;
                    self.expect(&TokenKind::Indent)?;
                    while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                        self.skip_newlines();
                        if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                            break;
                        }
                        let grant = self.collect_until_line_end();
                        if !grant.is_empty() {
                            gate.grants.push(grant);
                        }
                    }
                    self.expect(&TokenKind::Dedent)?;
                }
                _ => {
                    let line = self.collect_until_line_end();
                    if !line.is_empty() {
                        gate.body.push(line);
                    }
                }
            }
        }
        self.expect(&TokenKind::Dedent)?;
        gate.span = self.span_from_start(start);
        Ok(gate)
    }

    pub fn parse_sandbox_policy(&mut self) -> Result<SandboxPolicy, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("sandbox")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let mut items = Vec::new();
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            let item_start = self.current.span;
            let key = self.expect_identifier()?;
            let value = self.collect_until_line_end();
            if key == "backend" {
                items.push(SandboxItem::Backend {
                    name: value,
                    span: self.span_from_start(item_start),
                });
            } else {
                items.push(SandboxItem::Rule {
                    key,
                    value,
                    span: self.span_from_start(item_start),
                });
            }
        }
        self.expect(&TokenKind::Dedent)?;
        Ok(SandboxPolicy {
            name,
            items,
            span: self.span_from_start(start),
        })
    }

    pub fn parse_capability_policy(&mut self) -> Result<CapabilityPolicy, ParseError> {
        let start = self.current.span;
        self.expect_identifier_named("capability")?;
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;
        let mut items = Vec::new();
        while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
            self.skip_newlines();
            if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                break;
            }
            let item_start = self.current.span;
            let key = self.expect_identifier()?;
            let value = self.collect_security_clause_until_line_end();
            items.push(CapabilityItem::Rule {
                key,
                value,
                span: self.span_from_start(item_start),
            });
        }
        self.expect(&TokenKind::Dedent)?;
        Ok(CapabilityPolicy {
            name,
            items,
            span: self.span_from_start(start),
        })
    }

    fn collect_security_clause_until_line_end(&mut self) -> String {
        self.collect_security_clause_until_token(|kind| {
            matches!(kind, TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof)
        })
    }

    fn collect_security_clause_until_identifier(&mut self, expected: &str) -> String {
        self.collect_security_clause_until_token(
            |kind| matches!(kind, TokenKind::Identifier { name, .. } if name == expected),
        )
    }

    fn collect_security_clause_until_token<F>(&mut self, stop: F) -> String
    where
        F: Fn(&TokenKind) -> bool,
    {
        let mut value = String::new();
        let mut previous_was_word = false;
        while !stop(&self.current.kind) {
            if matches!(
                &self.current.kind,
                TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
            ) {
                break;
            }
            let current_is_word = self
                .current
                .lexeme
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_' || c == '"');
            if previous_was_word && current_is_word && !value.is_empty() {
                value.push(' ');
            }
            value.push_str(&self.current.lexeme);
            previous_was_word = current_is_word;
            self.advance();
        }
        value.trim().to_string()
    }

    /// Parse a DI binding: `bind on pc{...} -> <Impl> scope priority`
    pub fn parse_di_binding(&mut self) -> Result<DiBinding, ParseError> {
        let start = self.current.span;

        // Expect 'bind'
        self.expect(&TokenKind::Bind)?;

        // Expect 'on'
        self.expect(&TokenKind::On)?;

        // Parse pointcut predicate
        let pointcut = self.parse_pointcut()?;

        // Expect '->'
        self.expect(&TokenKind::Arrow)?;

        // Parse implementation name
        let implementation = self.expect_identifier()?;

        // Parse optional scope
        let scope = if let TokenKind::Identifier { name, .. } = &self.current.kind {
            match name.as_str() {
                "singleton" | "transient" | "scoped" => {
                    let scope_name = name.clone();
                    self.advance();
                    DiScope::parse_str(&scope_name)
                }
                _ => None,
            }
        } else {
            None
        };

        // Parse optional priority
        let priority = if let TokenKind::Identifier { name: s, .. } = &self.current.kind {
            if s == "priority" {
                self.advance(); // consume 'priority'
                if let TokenKind::Integer(val) = self.current.kind {
                    let v = val;
                    self.advance();
                    Some(v)
                } else {
                    return Err(ParseError::unexpected_token(
                        "integer",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
            } else {
                None
            }
        } else {
            None
        };

        let end = self.previous.span;
        Ok(DiBinding {
            pointcut,
            implementation,
            scope,
            priority,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    /// Parse an architecture rule: `forbid pc{...}` or `allow pc{...}`
    pub fn parse_arch_rule(&mut self) -> Result<ArchitectureRule, ParseError> {
        let start = self.current.span;

        // Parse rule type
        let rule_type = match &self.current.kind {
            TokenKind::Forbid => {
                self.advance();
                ArchRuleType::Forbid
            }
            TokenKind::Allow => {
                self.advance();
                ArchRuleType::Allow
            }
            _ => {
                return Err(ParseError::unexpected_token(
                    "forbid or allow",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            }
        };

        // Parse pointcut predicate
        let pointcut = self.parse_pointcut()?;

        // Parse optional message (string literal)
        let message = if matches!(&self.current.kind, TokenKind::String(_) | TokenKind::FString(_)) {
            match &self.current.kind {
                TokenKind::String(s) | TokenKind::RawString(s) => {
                    let value = s.clone();
                    self.advance();
                    Some(value)
                }
                TokenKind::FString(_) => {
                    let value = self.current.lexeme.clone();
                    self.advance();
                    Some(value)
                }
                _ => None,
            }
        } else {
            None
        };

        let end = self.previous.span;
        Ok(ArchitectureRule {
            rule_type,
            pointcut,
            message,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    /// Parse a mock declaration: `mock Name implements Trait:`
    pub fn parse_mock_decl(&mut self) -> Result<MockDecl, ParseError> {
        let start = self.current.span;

        // Expect 'mock'
        self.expect(&TokenKind::Mock)?;

        // Parse mock name
        let name = self.expect_identifier()?;

        // Expect 'implements'
        if let TokenKind::Identifier { name: s, .. } = &self.current.kind {
            if s != "implements" {
                return Err(ParseError::unexpected_token("implements", s.clone(), self.current.span));
            }
        } else {
            return Err(ParseError::unexpected_token(
                "implements",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }
        self.advance();

        // Parse trait name
        let trait_name = self.expect_identifier()?;

        // Expect ':'
        self.expect(&TokenKind::Colon)?;

        // Parse method expectations: expect method() -> Type:
        let mut expectations = Vec::new();

        // Expect INDENT
        if matches!(&self.current.kind, TokenKind::Indent) {
            self.advance();

            // Parse expectations until DEDENT
            while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                // Skip any newlines before the next expectation
                self.skip_newlines();

                // Check if we're at the end of the mock block
                if matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                    break;
                }

                // Parse a single expectation
                let expectation = self.parse_mock_expectation()?;
                expectations.push(expectation);

                // Skip newlines after the expectation
                self.skip_newlines();
            }

            // Expect DEDENT
            self.expect(&TokenKind::Dedent)?;
        }

        let end = self.previous.span;
        Ok(MockDecl {
            name,
            trait_name,
            expectations,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    /// Parse a mock expectation: `expect method_name(params) -> Type:`
    fn parse_mock_expectation(&mut self) -> Result<crate::ast::MockExpectation, ParseError> {
        let start = self.current.span;

        // Expect 'expect' keyword
        if let TokenKind::Identifier { name: s, .. } = &self.current.kind {
            if s != "expect" {
                return Err(ParseError::unexpected_token("expect", s.clone(), self.current.span));
            }
        } else {
            return Err(ParseError::unexpected_token(
                "expect",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }
        self.advance();

        // Parse method name
        let method_name = self.expect_identifier()?;

        // Parse parameters
        let params = self.parse_parameters()?;

        // Parse optional return type
        let return_type = if self.check(&TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        // Skip newlines before colon
        self.skip_newlines();

        // Expect ':'
        self.expect(&TokenKind::Colon)?;

        // After the colon, expect NEWLINE + INDENT to start the method body
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        // Parse the method body
        let body_block = self.parse_block_body()?;

        let end = self.previous.span;
        Ok(crate::ast::MockExpectation {
            method_name,
            params,
            return_type,
            body: body_block.statements,
            span: Span::new(start.start, end.end, start.line, start.column),
        })
    }

    /// Parse a pointcut predicate expression from a Pointcut token.
    ///
    /// The lexer has already extracted the content between pc{ and }, so we just
    /// need to parse the predicate expression itself.
    pub fn parse_pointcut(&mut self) -> Result<PredicateExpr, ParseError> {
        match &self.current.kind {
            TokenKind::Pointcut(content) => {
                let content = content.clone();
                let span = self.current.span;
                self.advance(); // consume the Pointcut token

                // Parse the predicate expression using the predicate parser
                self.parse_predicate_from_string(&content, span)
            }
            _ => Err(ParseError::unexpected_token(
                "pointcut expression 'pc{...}'",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Parse a predicate expression from a string (the content inside pc{...}).
    ///
    /// Grammar:
    /// ```text
    /// expr ::= or_expr
    /// or_expr ::= and_expr ('|' and_expr)*
    /// and_expr ::= not_expr ('&' not_expr)*
    /// not_expr ::= '!' not_expr | primary
    /// primary ::= selector '(' args ')' | '(' expr ')'
    /// ```
    fn parse_predicate_from_string(&self, content: &str, span: Span) -> Result<PredicateExpr, ParseError> {
        // LIMITATION: Simplified predicate parsing for early-stage compilation
        //
        // This creates a basic selector-only predicate. Full predicate parsing
        // (supporting boolean operations, function signatures, etc.) happens during
        // semantic analysis in simple_compiler::predicate_parser to avoid circular
        // dependencies between parser and compiler crates.
        //
        // Current behavior: Treats entire content as a selector name
        // Future: Parse full predicate grammar defined in grammar comment above
        Ok(PredicateExpr::selector(content.trim().to_string(), vec![], span))
    }

    // Helper methods

    /// Consume tokens until newline and return as string
    fn consume_until_newline(&mut self) -> String {
        let mut result = String::new();

        while !matches!(
            &self.current.kind,
            TokenKind::Newline | TokenKind::Dedent | TokenKind::Eof
        ) {
            result.push_str(&self.current.lexeme);
            result.push(' ');
            self.advance();
        }

        result.trim().to_string()
    }
}
