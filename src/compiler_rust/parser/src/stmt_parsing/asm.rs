//! Inline assembly parsing

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::super::Parser;

impl<'a> Parser<'a> {
    pub(crate) fn parse_asm(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Asm)?;

        if self.check(&TokenKind::Match) {
            return self.parse_asm_match(start_span);
        }

        let is_volatile = self.check_identifier("volatile");
        if is_volatile {
            self.advance();
        }

        if self.check(&TokenKind::LParen) {
            return self.parse_asm_parenthesized(start_span, is_volatile);
        }

        self.expect(&TokenKind::Colon)?;

        let mut instructions = Vec::new();
        let mut clobbers = Vec::new();

        if self.is_asm_string_token() {
            let instr = self.expect_string_value()?;
            instructions.push(instr);
            if self.check_identifier("clobbers") {
                self.advance();
                clobbers = self.parse_clobber_list()?;
            }
        } else if self.check(&TokenKind::Newline) {
            let block = self.parse_block()?;
            Self::extract_asm_block_strings(&block, &mut instructions);
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected string literal or indented block after 'asm:'".to_string(),
                self.current.span,
            ));
        }

        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            volatile: is_volatile,
            instructions,
            target_match: vec![],
            clobbers,
            constraints: vec![],
        }))
    }

    fn parse_asm_parenthesized(&mut self, start_span: Span, is_volatile: bool) -> Result<Node, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut instructions = Vec::new();
        let mut constraints = Vec::new();
        self.skip_asm_ws();

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            self.skip_asm_ws();
            if self.check(&TokenKind::RParen) { break; }

            if let Some(c) = self.try_parse_asm_constraint()? {
                constraints.push(c);
            } else if self.is_asm_string_token() {
                instructions.push(self.expect_string_value()?);
            } else {
                return Err(ParseError::syntax_error_with_span(
                    format!("expected string literal or asm constraint, got {:?}", self.current.kind),
                    self.current.span,
                ));
            }
            self.skip_asm_ws();
            if self.check(&TokenKind::Comma) { self.advance(); }
            self.skip_asm_ws();
        }

        self.expect(&TokenKind::RParen)?;
        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            volatile: is_volatile,
            instructions,
            target_match: vec![],
            clobbers: vec![],
            constraints,
        }))
    }

    fn try_parse_asm_constraint(&mut self) -> Result<Option<AsmConstraint>, ParseError> {
        let cs = self.current.span;
        if self.check(&TokenKind::In) && self.peek_is(&TokenKind::LParen) {
            return self.parse_asm_in_constraint(None, cs).map(Some);
        }
        if self.check(&TokenKind::Out) && self.peek_is(&TokenKind::LParen) {
            return self.parse_asm_out_constraint(None, cs).map(Some);
        }
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            let n = name.clone();
            match n.as_str() {
                "inout" | "lateout" | "clobber" | "clobber_abi" | "options" => {
                    return self.parse_asm_kw_constraint(&n, None, cs).map(Some);
                }
                _ => {}
            }
            if self.peek_is(&TokenKind::Assign) {
                let bname = n;
                self.advance();
                self.expect(&TokenKind::Assign)?;
                return self.parse_asm_dir(Some(bname), cs).map(Some);
            }
            return Ok(None);
        }
        if let Some(kw_name) = self.current.kind.keyword_name() {
            if self.peek_is(&TokenKind::Assign) {
                let bname = kw_name.to_string();
                self.advance();
                self.expect(&TokenKind::Assign)?;
                return self.parse_asm_dir(Some(bname), cs).map(Some);
            }
        }
        Ok(None)
    }

    fn parse_asm_kw_constraint(&mut self, kw: &str, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        self.advance();
        match kw {
            "inout" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_identifier()?;
                self.expect(&TokenKind::RParen)?;
                let op = self.parse_expression()?;
                Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: bname, kind: AsmConstraintKind::InOut, reg_class: Some(rc), operand: Some(op) })
            }
            "lateout" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_identifier()?;
                self.expect(&TokenKind::RParen)?;
                let op = self.parse_expression()?;
                Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: bname, kind: AsmConstraintKind::LateOut, reg_class: Some(rc), operand: Some(op) })
            }
            "clobber" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_identifier()?;
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: bname, kind: AsmConstraintKind::Clobber, reg_class: Some(rc), operand: None })
            }
            "clobber_abi" => {
                self.expect(&TokenKind::LParen)?;
                let abi = self.expect_string_value()?;
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: None, kind: AsmConstraintKind::ClobberAbi(abi), reg_class: None, operand: None })
            }
            "options" => {
                self.expect(&TokenKind::LParen)?;
                let mut opts = Vec::new();
                while !self.check(&TokenKind::RParen) {
                    opts.push(self.expect_identifier()?);
                    if !self.check(&TokenKind::RParen) { self.expect(&TokenKind::Comma)?; }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: None, kind: AsmConstraintKind::Options(opts), reg_class: None, operand: None })
            }
            _ => Err(ParseError::syntax_error_with_span(format!("unexpected asm keyword: {}", kw), self.current.span))
        }
    }

    fn parse_asm_dir(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        if self.check(&TokenKind::In) { return self.parse_asm_in_constraint(bname, cs); }
        if self.check(&TokenKind::Out) { return self.parse_asm_out_constraint(bname, cs); }
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            let kw = name.clone();
            match kw.as_str() {
                "inout" | "lateout" | "clobber" | "clobber_abi" | "options" => {
                    return self.parse_asm_kw_constraint(&kw, bname, cs);
                }
                _ => {}
            }
        }
        Err(ParseError::syntax_error_with_span("expected asm constraint direction".to_string(), self.current.span))
    }

    fn parse_asm_in_constraint(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        self.expect(&TokenKind::In)?;
        self.expect(&TokenKind::LParen)?;
        let rc = self.expect_identifier()?;
        self.expect(&TokenKind::RParen)?;
        let op = self.parse_expression()?;
        Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: bname, kind: AsmConstraintKind::In, reg_class: Some(rc), operand: Some(op) })
    }

    fn parse_asm_out_constraint(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        self.expect(&TokenKind::Out)?;
        self.expect(&TokenKind::LParen)?;
        let rc = self.expect_identifier()?;
        self.expect(&TokenKind::RParen)?;
        let op = self.parse_expression()?;
        Ok(AsmConstraint { span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column), name: bname, kind: AsmConstraintKind::Out, reg_class: Some(rc), operand: Some(op) })
    }

    fn extract_asm_block_strings(block: &Block, instructions: &mut Vec<String>) {
        for stmt in &block.statements {
            match stmt {
                Node::Expression(Expr::String(s)) => instructions.push(s.clone()),
                Node::Expression(Expr::FString { parts, .. }) => {
                    let mut text = String::new();
                    for part in parts {
                        match part {
                            FStringPart::Literal(s) => text.push_str(s),
                            FStringPart::Expr(e) => text.push_str(&format!("{:?}", e)),
                        }
                    }
                    instructions.push(text);
                }
                _ => {}
            }
        }
    }

    fn parse_asm_match(&mut self, start_span: Span) -> Result<Node, ParseError> {
        self.expect(&TokenKind::Match)?;
        self.expect(&TokenKind::Colon)?;
        let block = self.parse_block()?;
        let mut arms = Vec::new();
        for stmt in &block.statements {
            if let Node::Match(match_stmt) = stmt {
                for arm in &match_stmt.arms {
                    let target = match &arm.pattern {
                        Pattern::Literal(expr) => {
                            if let Expr::String(s) = expr.as_ref() { s.clone() } else { "_".to_string() }
                        }
                        Pattern::Wildcard => "_".to_string(),
                        Pattern::Identifier(name) => name.clone(),
                        _ => "_".to_string(),
                    };
                    let mut instrs = Vec::new();
                    for body_stmt in &arm.body.statements {
                        if let Node::Expression(Expr::String(s)) = body_stmt { instrs.push(s.clone()); }
                    }
                    arms.push(AsmTargetArm { span: arm.span, target, instructions: instrs });
                }
            }
        }
        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
            volatile: false, instructions: vec![], target_match: arms, clobbers: vec![], constraints: vec![],
        }))
    }

    fn parse_clobber_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut clobbers = Vec::new();
        while !self.check(&TokenKind::RBracket) {
            clobbers.push(self.expect_identifier()?);
            if !self.check(&TokenKind::RBracket) { self.expect(&TokenKind::Comma)?; }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(clobbers)
    }

    fn expect_string_value(&mut self) -> Result<String, ParseError> {
        match &self.current.kind {
            TokenKind::String(s) => { let s = s.clone(); self.advance(); Ok(s) }
            TokenKind::RawString(s) => { let s = s.clone(); self.advance(); Ok(s) }
            TokenKind::FString(parts) => {
                let mut text = String::new();
                for part in parts {
                    match part {
                        crate::token::FStringToken::Literal(s) => text.push_str(s),
                        crate::token::FStringToken::Expr(e) => text.push_str(e),
                    }
                }
                self.advance(); Ok(text)
            }
            _ => Err(ParseError::unexpected_token("string literal", format!("{:?}", self.current.kind), self.current.span))
        }
    }

    fn check_identifier(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier { name: n, .. } if n == name)
    }

    fn is_asm_string_token(&self) -> bool {
        matches!(self.current.kind, TokenKind::String(_) | TokenKind::RawString(_) | TokenKind::FString(_))
    }

    fn skip_asm_ws(&mut self) {
        while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent) {
            self.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    fn parse_succeeds(source: &str) {
        let mut parser = crate::Parser::new(source);
        match parser.parse() {
            Ok(_) => {}
            Err(e) => panic!("parse failed: {:?}", e),
        }
    }

    #[test]
    fn test_asm_volatile_single() {
        parse_succeeds("fn test():\n    asm volatile: \"cpsie i\"\n");
    }

    #[test]
    fn test_asm_volatile_block() {
        parse_succeeds("fn test():\n    asm volatile:\n        \"mov r0, r1\"\n        \"add r0, r2\"\n");
    }

    #[test]
    fn test_asm_volatile_paren_simple() {
        parse_succeeds("fn test():\n    asm volatile(\n        \"mov r0, r1\",\n        \"bkpt #0xAB\"\n    )\n");
    }

    #[test]
    fn test_asm_volatile_paren_constraints() {
        let source = "fn test(op: u32, pp: u32):\n    var result: i64 = 0\n    asm volatile(\n        \"mov r0, {op}\",\n        \"bkpt #0xAB\",\n        op = in(reg) op,\n        params = in(reg) pp,\n        result = out(reg) result,\n        clobber_abi(\"C\")\n    )\n";
        parse_succeeds(source);
    }

    #[test]
    fn test_asm_volatile_paren_options() {
        parse_succeeds("fn test():\n    asm volatile(\n        \"csrsi mstatus, 0x8\",\n        options(nostack)\n    )\n");
    }

    #[test]
    fn test_asm_non_volatile_works() {
        parse_succeeds("fn test():\n    asm: \"nop\"\n");
    }

    #[test]
    fn test_asm_volatile_out() {
        parse_succeeds("fn test():\n    var m: u32 = 0\n    asm volatile(\n        \"csrrci {m}, mstatus, 0x8\",\n        m = out(reg) m\n    )\n");
    }

    #[test]
    fn test_asm_volatile_unnamed_in() {
        parse_succeeds("fn test(x: u64):\n    asm volatile(\n        \"csrc mip, {msie}\",\n        in(reg) x\n    )\n");
    }

    #[test]
    fn test_fixed_size_array_type() {
        parse_succeeds("fn test():\n    var params: [i64; 2] = [1, 2]\n");
    }

    #[test]
    fn test_fixed_size_array_u32() {
        parse_succeeds("fn test():\n    var params: [u32; 3] = [1, 2, 3]\n");
    }

    #[test]
    fn test_cfg_decorated_asm() {
        let source = concat!(
            "fn test(op: u32, params_ptr: u32) -> i64:\n",
            "    var result: i64 = 0\n",
            "    @cfg(\"target_feature\", \"thumb\")\n",
            "    asm volatile(\n",
            "        \"bkpt #0xAB\",\n",
            "        op = in(reg) op,\n",
            "        result = out(reg) result\n",
            "    )\n",
            "    result\n",
        );
        parse_succeeds(source);
    }

    #[test]
    fn test_volatile_memory_access() {
        let source = concat!(
            "fn copy_data(src: u32, dst: u32):\n",
            "    unsafe:\n",
            "        val src_addr = @address(src as u64) @volatile val: u32\n",
            "        val dst_addr = @address(dst as u64) @volatile var: u32\n",
            "        dst_addr = src_addr\n",
        );
        parse_succeeds(source);
    }

    #[test]
    fn test_volatile_literal_address() {
        let source = concat!(
            "fn read_register():\n",
            "    unsafe:\n",
            "        val cfsr = @address(0xE000ED28) @volatile val: u32\n",
        );
        parse_succeeds(source);
    }

    #[test]
    fn test_volatile_complex_address() {
        let source = concat!(
            "fn write_vga(offset: u32):\n",
            "    val VGA_BUFFER: u64 = 0xB8000\n",
            "    unsafe:\n",
            "        val buffer = @address(VGA_BUFFER + offset as u64) @volatile var: u16\n",
            "        buffer = 0x0F41\n",
        );
        parse_succeeds(source);
    }
}
