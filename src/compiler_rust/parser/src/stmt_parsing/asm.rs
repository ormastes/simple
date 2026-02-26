//! Inline assembly parsing
//!
//! Parses:
//! - `asm: "single instruction"`
//! - `asm: block` (multi-line)
//! - `asm match: case [target]: instructions` (target-conditional)
//! - `asm "instruction" clobbers [reg1, reg2]` (with clobber list)

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::super::Parser;

impl<'a> Parser<'a> {
    /// Parse an inline assembly statement.
    /// Syntax:
    ///   asm: "mov rax, rbx"
    ///   asm:
    ///       "mov rax, rbx"
    ///       "add rax, 1"
    ///   asm match:
    ///       case "x86_64":
    ///           "mov rax, rbx"
    ///       case "aarch64":
    ///           "mov x0, x1"
    ///       case _:
    ///           pass
    pub(crate) fn parse_asm(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Asm)?;

        // Check for `asm match:` (target-conditional)
        if self.check(&TokenKind::Match) {
            return self.parse_asm_match(start_span);
        }

        self.expect(&TokenKind::Colon)?;

        // Check for inline single instruction vs block
        let mut instructions = Vec::new();
        let mut clobbers = Vec::new();

        if matches!(self.current.kind, TokenKind::String(_) | TokenKind::RawString(_)) {
            // Single inline instruction: asm: "mov rax, rbx"
            let instr = self.expect_string_value()?;
            instructions.push(instr);

            // Optional clobbers: asm: "..." clobbers [reg1, reg2]
            if self.check_identifier("clobbers") {
                self.advance();
                clobbers = self.parse_clobber_list()?;
            }
        } else if self.check(&TokenKind::Newline) {
            // Block form
            let block = self.parse_block()?;
            for stmt in &block.statements {
                match stmt {
                    Node::Expression(Expr::String(s)) => instructions.push(s.clone()),
                    Node::Expression(Expr::FString { parts, .. }) => {
                        // Collect fstring as raw text for now
                        let mut text = String::new();
                        for part in parts {
                            match part {
                                FStringPart::Literal(s) => text.push_str(s),
                                FStringPart::Expr(e) => text.push_str(&format!("{:?}", e)),
                            }
                        }
                        instructions.push(text);
                    }
                    _ => {
                        // Skip non-string statements (pass, etc.)
                    }
                }
            }
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected string literal or indented block after 'asm:'".to_string(),
                self.current.span,
            ));
        }

        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            instructions,
            target_match: vec![],
            clobbers,
        }))
    }

    /// Parse `asm match:` target-conditional assembly
    fn parse_asm_match(&mut self, start_span: Span) -> Result<Node, ParseError> {
        self.expect(&TokenKind::Match)?;
        self.expect(&TokenKind::Colon)?;

        let block = self.parse_block()?;
        let mut arms = Vec::new();

        for stmt in &block.statements {
            // Each statement should be a case arm parsed from the block
            // For now, we parse them as pass-through
            if let Node::Match(match_stmt) = stmt {
                for arm in &match_stmt.arms {
                    let target = match &arm.pattern {
                        Pattern::Literal(expr) => {
                            if let Expr::String(s) = expr.as_ref() {
                                s.clone()
                            } else {
                                "_".to_string()
                            }
                        }
                        Pattern::Wildcard => "_".to_string(),
                        Pattern::Identifier(name) => name.clone(),
                        _ => "_".to_string(),
                    };

                    let mut instrs = Vec::new();
                    for body_stmt in &arm.body.statements {
                        if let Node::Expression(Expr::String(s)) = body_stmt {
                            instrs.push(s.clone());
                        }
                    }

                    arms.push(AsmTargetArm {
                        span: arm.span,
                        target,
                        instructions: instrs,
                    });
                }
            }
        }

        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            instructions: vec![],
            target_match: arms,
            clobbers: vec![],
        }))
    }

    /// Parse clobber list: `[reg1, reg2, ...]`
    fn parse_clobber_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut clobbers = Vec::new();

        while !self.check(&TokenKind::RBracket) {
            let reg = self.expect_identifier()?;
            clobbers.push(reg);
            if !self.check(&TokenKind::RBracket) {
                self.expect(&TokenKind::Comma)?;
            }
        }

        self.expect(&TokenKind::RBracket)?;
        Ok(clobbers)
    }

    /// Helper: expect a string literal and return its value
    fn expect_string_value(&mut self) -> Result<String, ParseError> {
        match &self.current.kind {
            TokenKind::String(s) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            TokenKind::RawString(s) => {
                let s = s.clone();
                self.advance();
                Ok(s)
            }
            TokenKind::FString(parts) => {
                // Flatten fstring to text
                let mut text = String::new();
                for part in parts {
                    match part {
                        crate::token::FStringToken::Literal(s) => text.push_str(s),
                        crate::token::FStringToken::Expr(e) => text.push_str(e),
                    }
                }
                self.advance();
                Ok(text)
            }
            _ => Err(ParseError::unexpected_token(
                "string literal",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }

    /// Helper: check if current token is an identifier with given name
    fn check_identifier(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier { name: n, .. } if n == name)
    }
}
