//! Macro definition parsing
//!
//! This module handles parsing of macro definitions including:
//! - Macro parameters
//! - Contract items (returns, intro, inject)
//! - Macro targets and anchors
//! - Macro bodies and statements

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};
use crate::parser_impl::core::Parser;

impl<'a> Parser<'a> {
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

    pub(super) fn parse_macro_contract_items(
        &mut self,
    ) -> Result<Vec<MacroContractItem>, ParseError> {
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

    pub(super) fn parse_macro_contract_item(&mut self) -> Result<MacroContractItem, ParseError> {
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
            // Skip newlines and indents after colon
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                self.advance();
            }
            let spec = self.parse_macro_intro_spec()?;
            Ok(MacroContractItem::Intro(MacroIntro { label, spec }))
        } else if self.check_ident("inject") {
            self.advance();
            let label = self.expect_identifier()?;
            self.expect(&TokenKind::Colon)?;
            // Skip newlines and indents after colon
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                self.advance();
            }
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

    pub(super) fn parse_macro_intro_spec(&mut self) -> Result<MacroIntroSpec, ParseError> {
        if self.check(&TokenKind::For) {
            self.advance();
            let name = self.expect_identifier()?;
            self.expect(&TokenKind::In)?;
            // Use parse_primary to avoid consuming .. operator as part of expression
            let start = self.parse_primary()?;
            let inclusive = if self.check(&TokenKind::DoubleDotEq) {
                self.advance();
                true
            } else {
                self.expect(&TokenKind::DoubleDot)?;
                false
            };
            let end = self.parse_primary()?;
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

    pub(super) fn parse_macro_intro_spec_block(
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

    pub(super) fn parse_macro_intro_decl(&mut self) -> Result<MacroIntroDecl, ParseError> {
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

    pub(super) fn parse_macro_inject_spec(&mut self) -> Result<MacroInjectSpec, ParseError> {
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

    pub(super) fn parse_macro_target(&mut self) -> Result<MacroTarget, ParseError> {
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

    pub(super) fn parse_macro_anchor(&mut self) -> Result<MacroAnchor, ParseError> {
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

    pub(super) fn parse_macro_intro_kind(&mut self) -> Result<MacroIntroKind, ParseError> {
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

    pub(super) fn parse_macro_qident(&mut self) -> Result<String, ParseError> {
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

    pub(super) fn strip_macro_qident_quotes(&self, input: &str) -> String {
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

    pub(super) fn parse_macro_param_sig_list(&mut self) -> Result<Vec<MacroParamSig>, ParseError> {
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

    pub(super) fn parse_macro_body(&mut self) -> Result<Vec<MacroStmt>, ParseError> {
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
}
