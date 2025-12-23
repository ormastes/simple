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
    AdviceType, AopAdvice, ArchRuleType, ArchitectureRule, DiBinding, DiScope, MockDecl,
    PredicateExpr,
};
use crate::error::ParseError;
use crate::parser::Parser;
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
        let advice_type = if let TokenKind::Identifier(name) = &self.current.kind {
            match name.as_str() {
                "before" | "after_success" | "after_error" | "around" => {
                    let type_name = name.clone();
                    self.advance();
                    AdviceType::from_str(&type_name).ok_or_else(|| {
                        ParseError::unexpected_token(
                            "valid advice type",
                            type_name,
                            self.previous.span,
                        )
                    })?
                }
                _ => AdviceType::Before, // Default
            }
        } else {
            AdviceType::Before
        };

        // Parse optional priority
        let priority = if let TokenKind::Identifier(s) = &self.current.kind {
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
        let scope = if let TokenKind::Identifier(name) = &self.current.kind {
            match name.as_str() {
                "singleton" | "transient" | "scoped" => {
                    let scope_name = name.clone();
                    self.advance();
                    DiScope::from_str(&scope_name)
                }
                _ => None,
            }
        } else {
            None
        };

        // Parse optional priority
        let priority = if let TokenKind::Identifier(s) = &self.current.kind {
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
        let message = if matches!(&self.current.kind, TokenKind::String(_) | TokenKind::FString(_))
        {
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
        if let TokenKind::Identifier(s) = &self.current.kind {
            if s != "implements" {
                return Err(ParseError::unexpected_token(
                    "implements",
                    s.clone(),
                    self.current.span,
                ));
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

        // Parse method expectations (simplified for now - just store as strings)
        let mut expectations = Vec::new();

        // Expect INDENT
        if matches!(&self.current.kind, TokenKind::Indent) {
            self.advance();

            // Parse expectations until DEDENT
            while !matches!(&self.current.kind, TokenKind::Dedent | TokenKind::Eof) {
                // For now, just consume the line as a string
                // TODO: Proper parsing of expect method() -> Type: syntax
                let exp_line = self.consume_until_newline();
                expectations.push(exp_line);

                // Skip newlines
                while matches!(&self.current.kind, TokenKind::Newline) {
                    self.advance();
                }
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
    /// ```
    /// expr ::= or_expr
    /// or_expr ::= and_expr ('|' and_expr)*
    /// and_expr ::= not_expr ('&' not_expr)*
    /// not_expr ::= '!' not_expr | primary
    /// primary ::= selector '(' args ')' | '(' expr ')'
    /// ```
    fn parse_predicate_from_string(
        &self,
        content: &str,
        span: Span,
    ) -> Result<PredicateExpr, ParseError> {
        // TODO: Implement a simple inline predicate parser here
        // For now, create a simple selector as placeholder
        // The full predicate parser is in the compiler crate (simple_compiler::predicate_parser)
        // and will be used during compilation/semantic analysis

        // Simple placeholder: treat the entire content as a selector name
        Ok(PredicateExpr::selector(
            content.trim().to_string(),
            vec![],
            span,
        ))
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
