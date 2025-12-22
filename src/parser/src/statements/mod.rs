//! Statement parsing module
//!
//! This module contains all statement parsing logic including:
//! - Variable declarations (let, mut let, const, static)
//! - Control flow (if, for, while, loop, match)
//! - Jump statements (return, break, continue)
//! - Context and with statements
//! - Contract blocks (requires/ensures/invariant) - LLM-friendly feature #400
//! - Gherkin-style system test DSL (feature/scenario/examples) - Features #606-610

mod bounds;
mod contract;
mod gherkin;
mod var_decl;

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::Parser;

impl<'a> Parser<'a> {
    /// Helper to parse a number (float or int) as f64.
    fn parse_number_as_f64(&mut self) -> Result<f64, ParseError> {
        if let TokenKind::Float(f) = &self.current.kind {
            let val = *f;
            self.advance();
            Ok(val)
        } else if let TokenKind::Integer(i) = &self.current.kind {
            let val = *i as f64;
            self.advance();
            Ok(val)
        } else {
            Err(ParseError::unexpected_token(
                "number",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Helper to parse a unit variant (suffix = factor)
    fn parse_unit_variant(&mut self) -> Result<UnitVariant, ParseError> {
        let suffix = self.expect_identifier()?;
        self.expect(&TokenKind::Assign)?;
        let factor = self.parse_number_as_f64()?;
        Ok(UnitVariant { suffix, factor })
    }

    // === Control Flow ===

    pub(crate) fn parse_if(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::If)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let then_block = self.parse_block()?;

        let mut elif_branches = Vec::new();
        while self.check(&TokenKind::Elif) {
            self.advance();
            let elif_condition = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let elif_block = self.parse_block()?;
            elif_branches.push((elif_condition, elif_block));
        }

        let else_block = if self.check(&TokenKind::Else) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            Some(self.parse_block()?)
        } else {
            None
        };

        Ok(Node::If(IfStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            then_block,
            elif_branches,
            else_block,
        }))
    }

    pub(crate) fn parse_for(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::For)?;

        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::For(ForStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            iterable,
            body,
        }))
    }

    pub(crate) fn parse_while(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::While)?;

        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::While(WhileStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            let_pattern,
            condition,
            body,
        }))
    }

    pub(crate) fn parse_loop(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Loop)?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Loop(LoopStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            body,
        }))
    }

    pub(crate) fn parse_context(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        let context = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::Context(ContextStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            context,
            body,
        }))
    }

    pub(crate) fn parse_with(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::With)?;

        let mut resource = self.parse_expression()?;
        let mut alias_from_cast: Option<String> = None;
        // Handle "with expr as name:" where "as name" was parsed as a type cast
        // We detect this by checking if target_type is a simple lowercase identifier (variable name)
        // rather than an actual type (which would be capitalized or a primitive like i64, str, etc.)
        if let Expr::Cast { expr, target_type } = resource.clone() {
            if let Type::Simple(type_name) = target_type {
                // Check if it looks like a variable name (lowercase first char) rather than a type
                let first_char = type_name.chars().next().unwrap_or('A');
                let is_primitive = matches!(type_name.as_str(),
                    "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" |
                    "f32" | "f64" | "bool" | "str" | "nil" | "char");
                if first_char.is_lowercase() && !is_primitive {
                    alias_from_cast = Some(type_name);
                    resource = *expr;
                }
            }
        }

        // Optional "as name"
        let name = if self.check(&TokenKind::As) {
            self.advance();
            Some(self.expect_identifier()?)
        } else {
            alias_from_cast
        };

        self.expect(&TokenKind::Colon)?;
        let body = self.parse_block()?;

        Ok(Node::With(WithStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            resource,
            name,
            body,
        }))
    }

    // === Jump Statements ===

    pub(crate) fn parse_return(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Return)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Return(ReturnStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_break(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Break)?;

        let value = if !self.check(&TokenKind::Newline) && !self.is_at_end() {
            Some(self.parse_expression()?)
        } else {
            None
        };

        Ok(Node::Break(BreakStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            value,
        }))
    }

    pub(crate) fn parse_continue(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Continue)?;

        Ok(Node::Continue(ContinueStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
        }))
    }

    // === Match ===

    pub(crate) fn parse_match_stmt(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Match)?;

        let subject = self.parse_expression()?;
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut arms = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) {
                break;
            }
            arms.push(self.parse_match_arm()?);
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Match(MatchStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            subject,
            arms,
        }))
    }

    pub(crate) fn parse_match_arm(&mut self) -> Result<MatchArm, ParseError> {
        let start_span = self.current.span;
        if self.check(&TokenKind::Case) {
            self.advance();
        }
        let pattern = self.parse_pattern()?;

        let guard = if self.check(&TokenKind::If) {
            self.advance();
            Some(self.parse_expression()?)
        } else {
            None
        };

        let body = if self.check(&TokenKind::FatArrow) {
            self.advance();
            // Body can be single expression or block
            if self.check(&TokenKind::Newline) {
                self.parse_block()?
            } else {
                let expr = self.parse_expression()?;
                Block {
                    span: self.previous.span,
                    statements: vec![Node::Expression(expr)],
                }
            }
        } else if self.check(&TokenKind::Colon) {
            self.advance();
            self.parse_block()?
        } else {
            return Err(ParseError::unexpected_token(
                "match arm",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        Ok(MatchArm {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            pattern,
            guard,
            body,
        })
    }

    // === Macro Definition ===

    /// Parse a macro definition: macro name(params) -> (contract): body
    pub(crate) fn parse_macro_def(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Macro)?;

        let name = self.expect_identifier()?;

        // Parse macro parameters
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) {
            let param = self.parse_macro_param()?;
            params.push(param);
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Arrow)?;
        self.expect(&TokenKind::LParen)?;
        let contract = self.parse_macro_contract_items()?;
        self.expect(&TokenKind::RParen)?;
        self.expect(&TokenKind::Colon)?;

        let body = self.parse_macro_body()?;

        Ok(Node::Macro(MacroDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            params,
            contract,
            body,
            visibility: Visibility::Private,
        }))
    }

    /// Parse a single macro parameter: name: Type [const]
    pub(crate) fn parse_macro_param(&mut self) -> Result<MacroParam, ParseError> {
        let name = self.expect_identifier()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type()?;
        let is_const = if self.check(&TokenKind::Const) {
            self.advance();
            true
        } else {
            false
        };
        Ok(MacroParam { name, ty, is_const })
    }

    fn parse_macro_contract_items(&mut self) -> Result<Vec<MacroContractItem>, ParseError> {
        let mut items = Vec::new();
        while !self.check(&TokenKind::RParen) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::RParen) || self.is_at_end() {
                break;
            }
            items.push(self.parse_macro_contract_item()?);
            if self.check(&TokenKind::Comma) {
                self.advance();
            }
        }
        Ok(items)
    }

    fn parse_macro_contract_item(&mut self) -> Result<MacroContractItem, ParseError> {
        if self.check_ident("returns") {
            self.advance();
            let label = if self.peek_is(&TokenKind::Colon) {
                match &self.current.kind {
                    TokenKind::Identifier(_) => Some(self.expect_identifier()?),
                    TokenKind::Result => {
                        let name = self.current.lexeme.clone();
                        self.advance();
                        Some(name)
                    }
                    _ => None,
                }
            } else {
                None
            };
            self.expect(&TokenKind::Colon)?;
            let ty = self.parse_type()?;
            Ok(MacroContractItem::Returns(MacroReturns { label, ty }))
        } else if self.check_ident("intro") {
            self.advance();
            let label = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            let spec = self.parse_macro_intro_spec()?;
            Ok(MacroContractItem::Intro(MacroIntro { label, spec }))
        } else if self.check_ident("inject") {
            self.advance();
            let label = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            let spec = self.parse_macro_inject_spec()?;
            Ok(MacroContractItem::Inject(MacroInject { label, spec }))
        } else {
            Err(ParseError::unexpected_token(
                "contract item (returns, intro, inject)",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn parse_macro_intro_spec(&mut self) -> Result<MacroIntroSpec, ParseError> {
        if self.check(&TokenKind::For) {
            self.advance();
            let name = self.expect_identifier()?;
            self.expect(&TokenKind::In)?;
            let start = self.parse_expression()?;
            let inclusive = if self.check(&TokenKind::DoubleDotEq) {
                self.advance();
                true
            } else {
                self.expect(&TokenKind::DoubleDot)?;
                false
            };
            let end = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let body = self.parse_macro_intro_spec_block(&[TokenKind::Comma, TokenKind::RParen])?;
            Ok(MacroIntroSpec::For {
                name,
                range: MacroConstRange { start, end, inclusive },
                body,
            })
        } else if self.check(&TokenKind::If) {
            self.advance();
            let condition = self.parse_expression()?;
            self.expect(&TokenKind::Colon)?;
            let then_body = self.parse_macro_intro_spec_block(&[
                TokenKind::Else,
                TokenKind::Comma,
                TokenKind::RParen,
            ])?;
            let else_body = if self.check(&TokenKind::Else) {
                self.advance();
                self.expect(&TokenKind::Colon)?;
                self.parse_macro_intro_spec_block(&[TokenKind::Comma, TokenKind::RParen])?
            } else {
                Vec::new()
            };
            Ok(MacroIntroSpec::If {
                condition,
                then_body,
                else_body,
            })
        } else {
            let decl = self.parse_macro_intro_decl()?;
            Ok(MacroIntroSpec::Decl(decl))
        }
    }

    fn parse_macro_intro_spec_block(
        &mut self,
        terminators: &[TokenKind],
    ) -> Result<Vec<MacroIntroSpec>, ParseError> {
        let mut specs = Vec::new();
        loop {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.is_at_end() || terminators.iter().any(|t| self.check(t)) {
                break;
            }
            specs.push(self.parse_macro_intro_spec()?);
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }
        Ok(specs)
    }

    fn parse_macro_intro_decl(&mut self) -> Result<MacroIntroDecl, ParseError> {
        let target = self.parse_macro_target()?;
        self.expect(&TokenKind::Dot)?;
        let kind = self.parse_macro_intro_kind()?;
        let stub = match kind {
            MacroIntroKind::Fn => {
                let name = self.parse_macro_qident()?;
                let params = self.parse_macro_param_sig_list()?;
                let ret = if self.check(&TokenKind::Arrow) {
                    self.advance();
                    Some(self.parse_type()?)
                } else {
                    None
                };
                MacroDeclStub::Fn(MacroFnStub { name, params, ret })
            }
            MacroIntroKind::Field => {
                let name = self.parse_macro_qident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                MacroDeclStub::Field(MacroFieldStub { name, ty })
            }
            MacroIntroKind::Type => {
                let name = self.parse_macro_qident()?;
                MacroDeclStub::Type(MacroTypeStub { name })
            }
            MacroIntroKind::Let | MacroIntroKind::Const => {
                let name = self.parse_macro_qident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                MacroDeclStub::Var(MacroVarStub { name, ty })
            }
        };
        Ok(MacroIntroDecl { target, kind, stub })
    }

    fn parse_macro_inject_spec(&mut self) -> Result<MacroInjectSpec, ParseError> {
        self.expect_ident_value("callsite")?;
        self.expect(&TokenKind::Dot)?;
        self.expect_ident_value("block")?;
        self.expect(&TokenKind::Dot)?;
        let anchor = self.parse_macro_anchor()?;
        self.expect(&TokenKind::Dot)?;
        let code_kind = if self.check_ident("stmt") {
            self.advance();
            MacroCodeKind::Stmt
        } else if self.check_ident("block") {
            self.advance();
            MacroCodeKind::Block
        } else {
            return Err(ParseError::unexpected_token(
                "stmt or block",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };
        Ok(MacroInjectSpec { anchor, code_kind })
    }

    fn parse_macro_target(&mut self) -> Result<MacroTarget, ParseError> {
        if self.check_ident("enclosing") {
            self.advance();
            self.expect(&TokenKind::Dot)?;
            let enclosing = if self.check_ident("module") {
                self.advance();
                EnclosingTarget::Module
            } else if self.check(&TokenKind::Class) {
                self.advance();
                EnclosingTarget::Class
            } else if self.check(&TokenKind::Struct) {
                self.advance();
                EnclosingTarget::Struct
            } else if self.check(&TokenKind::Trait) {
                self.advance();
                EnclosingTarget::Trait
            } else {
                return Err(ParseError::unexpected_token(
                    "module, class, struct, or trait",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ));
            };
            Ok(MacroTarget::Enclosing(enclosing))
        } else if self.check_ident("callsite") {
            self.advance();
            self.expect(&TokenKind::Dot)?;
            self.expect_ident_value("block")?;
            self.expect(&TokenKind::Dot)?;
            let anchor = self.parse_macro_anchor()?;
            Ok(MacroTarget::CallsiteBlock(anchor))
        } else {
            Err(ParseError::unexpected_token(
                "enclosing or callsite",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn parse_macro_anchor(&mut self) -> Result<MacroAnchor, ParseError> {
        if self.check_ident("head") {
            self.advance();
            Ok(MacroAnchor::Head)
        } else if self.check_ident("tail") {
            self.advance();
            Ok(MacroAnchor::Tail)
        } else if self.check_ident("here") {
            self.advance();
            Ok(MacroAnchor::Here)
        } else {
            Err(ParseError::unexpected_token(
                "head, tail, or here",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn parse_macro_intro_kind(&mut self) -> Result<MacroIntroKind, ParseError> {
        if self.check(&TokenKind::Fn) {
            self.advance();
            Ok(MacroIntroKind::Fn)
        } else if self.check_ident("field") {
            self.advance();
            Ok(MacroIntroKind::Field)
        } else if self.check(&TokenKind::Type) {
            self.advance();
            Ok(MacroIntroKind::Type)
        } else if self.check(&TokenKind::Let) {
            self.advance();
            Ok(MacroIntroKind::Let)
        } else if self.check(&TokenKind::Const) {
            self.advance();
            Ok(MacroIntroKind::Const)
        } else {
            Err(ParseError::unexpected_token(
                "fn, field, type, let, or const",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    fn parse_macro_qident(&mut self) -> Result<String, ParseError> {
        match &self.current.kind {
            TokenKind::Identifier(_) => self.expect_identifier(),
            TokenKind::FString(_)
            | TokenKind::String(_)
            | TokenKind::RawString(_)
            | TokenKind::TypedString(_, _)
            | TokenKind::TypedRawString(_, _) => {
                let lexeme = self.current.lexeme.clone();
                self.advance();
                Ok(self.strip_macro_qident_quotes(&lexeme))
            }
            _ => Err(ParseError::unexpected_token(
                "identifier or string literal",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    fn strip_macro_qident_quotes(&self, input: &str) -> String {
        let bytes = input.as_bytes();
        if bytes.len() >= 2 {
            let first = bytes[0];
            let last = bytes[bytes.len() - 1];
            if (first == b'"' && last == b'"') || (first == b'\'' && last == b'\'') {
                return input[1..input.len() - 1].to_string();
            }
        }
        input.to_string()
    }

    fn parse_macro_param_sig_list(&mut self) -> Result<Vec<MacroParamSig>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) {
            let name = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            let ty = self.parse_type()?;
            params.push(MacroParamSig { name, ty });
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    fn parse_macro_body(&mut self) -> Result<Vec<MacroStmt>, ParseError> {
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut body = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            if self.check_ident("const_eval") {
                self.advance();
                self.expect(&TokenKind::Colon)?;
                let block = self.parse_block()?;
                body.push(MacroStmt::ConstEval(block));
            } else if self.check_ident("emit") {
                self.advance();
                let label = match &self.current.kind {
                    TokenKind::Identifier(_) => self.expect_identifier()?,
                    TokenKind::Result => {
                        let name = self.current.lexeme.clone();
                        self.advance();
                        name
                    }
                    _ => {
                        return Err(ParseError::unexpected_token(
                            "identifier",
                            format!("{:?}", self.current.kind),
                            self.current.span,
                        ));
                    }
                };
                self.expect(&TokenKind::Colon)?;
                let block = self.parse_block()?;
                body.push(MacroStmt::Emit { label, block });
            } else {
                let stmt = self.parse_item()?;
                body.push(MacroStmt::Stmt(stmt));
            }

            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        self.expect(&TokenKind::Dedent)?;
        Ok(body)
    }

    // === Module System (Features #104-111) ===

    /// Parse a module path: crate.sys.http.router
    /// Returns the segments as a vector
    pub(crate) fn parse_module_path(&mut self) -> Result<ModulePath, ParseError> {
        let mut segments = Vec::new();

        // First segment (could be 'crate' keyword or identifier)
        if self.check(&TokenKind::Crate) {
            self.advance();
            segments.push("crate".to_string());
        } else {
            // Use expect_path_segment to allow keywords like 'unit', 'test', etc.
            segments.push(self.expect_path_segment()?);
        }

        // Parse dot-separated segments
        while self.check(&TokenKind::Dot) {
            self.advance();

            // Check for glob: module.*
            if self.check(&TokenKind::Star) {
                break; // Stop, let caller handle *
            }

            // Check for group: module.{A, B}
            if self.check(&TokenKind::LBrace) {
                break; // Stop, let caller handle {}
            }

            // Use expect_path_segment to allow keywords as path segments
            segments.push(self.expect_path_segment()?);
        }

        Ok(ModulePath::new(segments))
    }

    /// Parse an import target: single item, alias, group, or glob
    /// Called after the module path is parsed
    pub(crate) fn parse_import_target(
        &mut self,
        last_segment: Option<String>,
    ) -> Result<ImportTarget, ParseError> {
        // Check for glob: *
        if self.check(&TokenKind::Star) {
            self.advance();
            return Ok(ImportTarget::Glob);
        }

        // Check for group: {A, B, C}
        if self.check(&TokenKind::LBrace) {
            self.advance();
            let mut targets = Vec::new();

            while !self.check(&TokenKind::RBrace) {
                let name = self.expect_identifier()?;
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_identifier()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);

                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RBrace)?;
            return Ok(ImportTarget::Group(targets));
        }

        // Single item (already parsed as last segment of path)
        if let Some(name) = last_segment {
            // Check for alias: as NewName
            if self.check(&TokenKind::As) {
                self.advance();
                let alias = self.expect_identifier()?;
                return Ok(ImportTarget::Aliased { name, alias });
            }
            return Ok(ImportTarget::Single(name));
        }

        Err(ParseError::unexpected_token(
            "import target",
            format!("{:?}", self.current.kind),
            self.current.span,
        ))
    }

    /// Parse use statement: use crate.module.Item
    /// use crate.module.{A, B}
    /// use crate.module.*
    /// use crate.module.Item as Alias
    pub(crate) fn parse_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Use)?;
        self.parse_use_or_import_body(start_span)
    }

    /// Parse import statement (alias for use): import module.Item
    /// This is syntactic sugar for `use` - both work identically.
    pub(crate) fn parse_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Import)?;
        self.parse_use_or_import_body(start_span)
    }

    /// Common body for use/import statements
    fn parse_use_or_import_body(&mut self, start_span: Span) -> Result<Node, ParseError> {
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse mod declaration: mod name or pub mod name
    pub(crate) fn parse_mod(
        &mut self,
        visibility: Visibility,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mod)?;
        let name = self.expect_identifier()?;
        Ok(Node::ModDecl(ModDecl {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            visibility,
            attributes,
        }))
    }

    /// Parse common use: common use crate.module.*
    pub(crate) fn parse_common_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Common)?;
        self.expect(&TokenKind::Use)?;
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::CommonUseStmt(CommonUseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse export use: export use router.Router
    pub(crate) fn parse_export_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Export)?;
        self.expect(&TokenKind::Use)?;
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::ExportUseStmt(ExportUseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse auto import: auto import router.route
    pub(crate) fn parse_auto_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Auto)?;
        self.expect(&TokenKind::Import)?;

        let path = self.parse_module_path()?;

        // Last segment is the macro name
        let mut segments = path.segments;
        let macro_name = segments.pop().unwrap_or_default();

        Ok(Node::AutoImportStmt(AutoImportStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path: ModulePath::new(segments),
            macro_name,
        }))
    }

    /// Parse requires capabilities statement: requires [pure, io, net]
    ///
    /// This declares the capabilities allowed in the current module.
    /// Must appear at the top of __init__.spl files.
    pub(crate) fn parse_requires_capabilities(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Requires)?;
        self.expect(&TokenKind::LBracket)?;

        let mut capabilities = Vec::new();

        // Parse capability list
        if !self.check(&TokenKind::RBracket) {
            loop {
                // Parse capability name as identifier
                let cap_name = self.expect_identifier()?;

                // Convert to Capability enum
                let capability = Capability::from_name(&cap_name).ok_or_else(|| {
                    ParseError::syntax_error_with_span(
                        format!(
                            "unknown capability '{}'. Valid capabilities: pure, io, net, fs, unsafe, gc",
                            cap_name
                        ),
                        self.previous.span,
                    )
                })?;

                capabilities.push(capability);

                // Check for comma or end
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Allow trailing comma
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RBracket)?;

        Ok(Node::RequiresCapabilities(RequiresCapabilitiesStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            capabilities,
        }))
    }
}
