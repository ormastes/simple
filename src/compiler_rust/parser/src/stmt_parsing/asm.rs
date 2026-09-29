//! Inline assembly parsing

use crate::ast::*;
use crate::error::ParseError;
use crate::error_recovery::ErrorHint;
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

        // Design A.4: `asm [volatile] clobbers(rax, rcx, memory) { ... }`.
        // The clobber list belongs to the raw braced form only.
        let mut braced_clobbers = Vec::new();
        if self.check_identifier("clobbers") {
            self.advance();
            braced_clobbers = self.parse_paren_clobber_list()?;
        }

        if self.check(&TokenKind::LParen) {
            return self.parse_asm_parenthesized(start_span, is_volatile);
        }

        if self.check(&TokenKind::LBrace) {
            return self.parse_asm_braced(start_span, is_volatile, braced_clobbers);
        }

        if self.is_asm_string_token() {
            self.warn_legacy_asm_syntax(start_span);
            let instr = self.expect_string_value()?;
            return Ok(Node::InlineAsm(InlineAsmStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                volatile: is_volatile,
                instructions: vec![instr],
                target_match: vec![],
                clobbers: vec![],
                constraints: vec![],
            }));
        }

        self.expect(&TokenKind::Colon)?;
        self.warn_legacy_asm_syntax(start_span);

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
            Self::extract_asm_block_strings(&block, &mut instructions, start_span)?;
        } else {
            return Err(ParseError::syntax_error_with_span(
                "expected string literal or indented block after 'asm:'".to_string(),
                self.current.span,
            ));
        }

        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            volatile: is_volatile,
            instructions,
            target_match: vec![],
            clobbers,
            constraints: vec![],
        }))
    }

    fn parse_asm_braced(
        &mut self,
        start_span: Span,
        is_volatile: bool,
        clobbers: Vec<String>,
    ) -> Result<Node, ParseError> {
        let open_span = self.current.span;
        self.expect(&TokenKind::LBrace)?;

        let content_start = open_span.end;
        let content_end = self.find_raw_asm_block_end(content_start)?;
        let close_end = self
            .source
            .get(content_end..)
            .and_then(|tail| tail.chars().next())
            .map(|ch| content_end + ch.len_utf8())
            .unwrap_or(content_end);
        let raw = self
            .source
            .get(content_start..content_end)
            .unwrap_or("")
            .trim()
            .to_string();
        let instructions = Self::normalize_raw_asm_instructions(&raw);

        while !self.check(&TokenKind::Eof) && self.current.span.start < close_end {
            self.advance();
        }

        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(start_span.start, close_end, start_span.line, start_span.column),
            volatile: is_volatile,
            instructions,
            target_match: vec![],
            clobbers,
            constraints: vec![],
        }))
    }

    /// `clobbers(rax, rcx, memory)` — parenthesized register/pseudo-register
    /// list of the raw braced form (design A.4). Names are validated later,
    /// at HIR lowering (E-ASM-CLOBBER), where the target is known.
    fn parse_paren_clobber_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut clobbers = Vec::new();
        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            clobbers.push(self.expect_identifier()?);
            if self.check(&TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(clobbers)
    }

    fn parse_asm_parenthesized(&mut self, start_span: Span, is_volatile: bool) -> Result<Node, ParseError> {
        self.warn_legacy_asm_syntax(start_span);
        self.expect(&TokenKind::LParen)?;
        let mut instructions = Vec::new();
        let mut constraints = Vec::new();
        self.skip_asm_ws();

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            self.skip_asm_ws();
            if self.check(&TokenKind::RParen) {
                break;
            }

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
            if self.check(&TokenKind::Comma) {
                self.advance();
            }
            self.skip_asm_ws();
        }

        self.expect(&TokenKind::RParen)?;
        Ok(Node::InlineAsm(InlineAsmStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            volatile: is_volatile,
            instructions,
            target_match: vec![],
            clobbers: vec![],
            constraints,
        }))
    }

    fn warn_legacy_asm_syntax(&mut self, span: Span) {
        self.error_hints.push(
            ErrorHint::warning("legacy inline asm syntax; use asm { ... }".to_string(), span)
                .with_suggestion("Use `asm { ... }` or `asm volatile { ... }`".to_string()),
        );
    }

    fn find_raw_asm_block_end(&self, content_start: usize) -> Result<usize, ParseError> {
        let mut depth = 1usize;
        let mut in_string: Option<char> = None;
        let mut escaped = false;

        for (offset, ch) in self.source[content_start..].char_indices() {
            let pos = content_start + offset;
            if let Some(quote) = in_string {
                if escaped {
                    escaped = false;
                } else if ch == '\\' {
                    escaped = true;
                } else if ch == quote {
                    in_string = None;
                }
                continue;
            }

            if ch == '"' || ch == '\'' {
                in_string = Some(ch);
                continue;
            }

            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(pos);
                    }
                }
                _ => {}
            }
        }

        Err(ParseError::syntax_error_with_span(
            "unterminated asm { ... } block".to_string(),
            Span::new(
                content_start,
                self.source.len(),
                self.current.span.line,
                self.current.span.column,
            ),
        ))
    }

    fn normalize_raw_asm_instructions(raw: &str) -> Vec<String> {
        raw.lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .map(|line| {
                let line = line.trim_end_matches([';', ',']).trim();
                if line.len() >= 2
                    && ((line.starts_with('"') && line.ends_with('"'))
                        || (line.starts_with('\'') && line.ends_with('\'')))
                {
                    line[1..line.len() - 1].to_string()
                } else {
                    line.to_string()
                }
            })
            .collect()
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

    fn parse_asm_kw_constraint(
        &mut self,
        kw: &str,
        bname: Option<String>,
        cs: Span,
    ) -> Result<AsmConstraint, ParseError> {
        self.advance();
        match kw {
            "inout" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_identifier()?;
                self.expect(&TokenKind::RParen)?;
                let op = self.parse_expression()?;
                Ok(AsmConstraint {
                    span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
                    name: bname,
                    kind: AsmConstraintKind::InOut,
                    reg_class: Some(rc),
                    operand: Some(op),
                })
            }
            "lateout" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_identifier()?;
                self.expect(&TokenKind::RParen)?;
                let op = self.parse_expression()?;
                Ok(AsmConstraint {
                    span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
                    name: bname,
                    kind: AsmConstraintKind::LateOut,
                    reg_class: Some(rc),
                    operand: Some(op),
                })
            }
            "clobber" => {
                self.expect(&TokenKind::LParen)?;
                let rc = self.expect_clobber_name()?;
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint {
                    span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
                    name: bname,
                    kind: AsmConstraintKind::Clobber,
                    reg_class: Some(rc),
                    operand: None,
                })
            }
            "clobber_abi" => {
                self.expect(&TokenKind::LParen)?;
                let abi = self.expect_string_value()?;
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint {
                    span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
                    name: None,
                    kind: AsmConstraintKind::ClobberAbi(abi),
                    reg_class: None,
                    operand: None,
                })
            }
            "options" => {
                self.expect(&TokenKind::LParen)?;
                let mut opts = Vec::new();
                while !self.check(&TokenKind::RParen) {
                    opts.push(self.expect_identifier()?);
                    if !self.check(&TokenKind::RParen) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(AsmConstraint {
                    span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
                    name: None,
                    kind: AsmConstraintKind::Options(opts),
                    reg_class: None,
                    operand: None,
                })
            }
            _ => Err(ParseError::syntax_error_with_span(
                format!("unexpected asm keyword: {}", kw),
                self.current.span,
            )),
        }
    }

    fn parse_asm_dir(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        if self.check(&TokenKind::In) {
            return self.parse_asm_in_constraint(bname, cs);
        }
        if self.check(&TokenKind::Out) {
            return self.parse_asm_out_constraint(bname, cs);
        }
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            let kw = name.clone();
            match kw.as_str() {
                "inout" | "lateout" | "clobber" | "clobber_abi" | "options" => {
                    return self.parse_asm_kw_constraint(&kw, bname, cs);
                }
                _ => {}
            }
        }
        Err(ParseError::syntax_error_with_span(
            "expected asm constraint direction".to_string(),
            self.current.span,
        ))
    }

    fn parse_asm_in_constraint(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        self.expect(&TokenKind::In)?;
        self.expect(&TokenKind::LParen)?;
        let rc = self.expect_identifier()?;
        self.expect(&TokenKind::RParen)?;
        let op = self.parse_expression()?;
        Ok(AsmConstraint {
            span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
            name: bname,
            kind: AsmConstraintKind::In,
            reg_class: Some(rc),
            operand: Some(op),
        })
    }

    fn parse_asm_out_constraint(&mut self, bname: Option<String>, cs: Span) -> Result<AsmConstraint, ParseError> {
        self.expect(&TokenKind::Out)?;
        self.expect(&TokenKind::LParen)?;
        let rc = self.expect_identifier()?;
        self.expect(&TokenKind::RParen)?;
        let op = self.parse_expression()?;
        Ok(AsmConstraint {
            span: Span::new(cs.start, self.previous.span.end, cs.line, cs.column),
            name: bname,
            kind: AsmConstraintKind::Out,
            reg_class: Some(rc),
            operand: Some(op),
        })
    }

    /// Render one `{...}` placeholder of an inline-asm template as an assembler
    /// token. Only literal-shaped operands have an unambiguous assembler
    /// spelling; anything else must be rejected loudly, because Debug-formatting
    /// it used to leak `Identifier("stack_top")` straight into emitted assembly
    /// (see `doc/08_tracking/bug/inline_asm_placeholder_debug_formatted_2026-08-17.md`).
    fn render_asm_placeholder(expr: &Expr) -> Option<String> {
        match expr {
            Expr::Identifier(name) => Some(name.clone()),
            Expr::Path(segments) => Some(segments.join("::")),
            Expr::Integer(v) => Some(v.to_string()),
            Expr::TypedInteger(v, _) => Some(v.to_string()),
            Expr::String(s) => Some(s.clone()),
            Expr::Bool(b) => Some(if *b { "1".to_string() } else { "0".to_string() }),
            _ => None,
        }
    }

    fn extract_asm_block_strings(block: &Block, instructions: &mut Vec<String>, span: Span) -> Result<(), ParseError> {
        for stmt in &block.statements {
            match stmt {
                Node::Expression(Expr::String(s)) => instructions.push(s.clone()),
                Node::Expression(Expr::FString { parts, .. }) => {
                    let mut text = String::new();
                    for part in parts {
                        match part {
                            FStringPart::Literal(s) => text.push_str(s),
                            FStringPart::Expr(e) | FStringPart::ExprWithFormat(e, _) => {
                                match Self::render_asm_placeholder(e) {
                                    // `{name}` / `{0}` in an asm template is an OPERAND
                                    // placeholder, not an interpolation — the same contract
                                    // `expect_string_value` documents for the parenthesized
                                    // form. The braces MUST survive parsing so MIR lowering
                                    // can rewrite them to LLVM's `$N`
                                    // (mir/asm_operands.rs::rewrite_asm_placeholders) and so
                                    // the C sidecar, which cannot bind operands, can
                                    // RECOGNISE an operand-bearing line and skip it.
                                    //
                                    // Flattening to the bare rendered token is what emitted
                                    // `csrr 0, mcause`, `mv out, tp` and `invlpg [addr]`
                                    // into the riscv64 WM translation unit — the assembler
                                    // sees an operand INDEX or a Simple local name where a
                                    // register belongs. See
                                    // doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md
                                    //
                                    // `render_asm_placeholder` is still called (and still
                                    // rejects unrenderable expressions loudly) so the
                                    // 2026-08-17 `Identifier("stack_top")` Debug-format leak
                                    // stays fixed: the key inside the braces is a plain
                                    // token, never a `{:?}` rendering.
                                    Some(rendered) => {
                                        text.push('{');
                                        text.push_str(&rendered);
                                        text.push('}');
                                    }
                                    None => {
                                        return Err(ParseError::syntax_error_with_span(
                                            format!(
                                                "unsupported operand in inline asm template placeholder: \
                                                 only identifiers, paths, integer/string/bool literals are \
                                                 allowed, got `{e:?}`"
                                            ),
                                            span,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                    instructions.push(text);
                }
                _ => {}
            }
        }
        Ok(())
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
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            volatile: false,
            instructions: vec![],
            target_match: arms,
            clobbers: vec![],
            constraints: vec![],
        }))
    }

    fn parse_clobber_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect(&TokenKind::LBracket)?;
        let mut clobbers = Vec::new();
        while !self.check(&TokenKind::RBracket) {
            clobbers.push(self.expect_identifier()?);
            if !self.check(&TokenKind::RBracket) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RBracket)?;
        Ok(clobbers)
    }

    /// Clobber name inside the parenthesized asm form: `clobber(memory)` or
    /// `clobber("memory")`. Both spellings are accepted because the two forms
    /// of the design doc disagree on purpose: the braced form
    /// (`asm volatile clobbers(rax, memory) { ... }`, design A.4) spells
    /// register names as bare identifiers, while the parenthesized operand form
    /// spells register-name arguments as STRINGS — `in("rax") arg`,
    /// `clobber_abi("C")` in
    /// `doc/05_design/language/language_features/syntax_features/inline_assembly_design.md`.
    /// `clobber("memory")` is the string spelling of that same form, and before
    /// this it was the only register-name argument in the parenthesized form
    /// that rejected a string. Validation of the NAME still happens once, at HIR
    /// lowering (`is_known_asm_clobber`, E-ASM-CLOBBER), where the target is
    /// known; this helper only decides the surface spelling.
    fn expect_clobber_name(&mut self) -> Result<String, ParseError> {
        if self.is_asm_string_token() {
            return self.expect_string_value();
        }
        self.expect_identifier()
    }

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
                let mut text = String::new();
                for part in parts {
                    match part {
                        crate::token::FStringToken::Literal(s) => text.push_str(s),
                        // `{name}` in an asm template is an OPERAND placeholder,
                        // not an interpolation: keep the braces so MIR lowering
                        // can rewrite it to LLVM's `$N` (mir/asm_operands.rs).
                        // Flattening to the bare name emitted `csrr result, sstatus`.
                        crate::token::FStringToken::Expr(e) => {
                            text.push('{');
                            text.push_str(e);
                            text.push('}');
                        }
                        crate::token::FStringToken::ExprWithFormat(e, spec) => {
                            text.push('{');
                            text.push_str(e);
                            text.push(':');
                            text.push_str(spec);
                            text.push('}');
                        }
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

    pub(crate) fn check_identifier(&self, name: &str) -> bool {
        matches!(&self.current.kind, TokenKind::Identifier { name: n, .. } if n == name)
    }

    fn is_asm_string_token(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::String(_) | TokenKind::RawString(_) | TokenKind::FString(_)
        )
    }

    fn skip_asm_ws(&mut self) {
        while matches!(
            self.current.kind,
            TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent
        ) {
            self.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Node;

    fn parse_succeeds(source: &str) {
        let mut parser = crate::Parser::new(source);
        match parser.parse() {
            Ok(_) => {}
            Err(e) => panic!("parse failed: {:?}", e),
        }
    }

    fn parse_first_asm(source: &str) -> crate::ast::InlineAsmStmt {
        let mut parser = crate::Parser::new(source);
        let module = parser.parse().expect("parse");
        let Node::Function(function) = &module.items[0] else {
            panic!("expected function");
        };
        let Node::InlineAsm(asm_stmt) = &function.body.statements[0] else {
            panic!("expected inline asm");
        };
        asm_stmt.clone()
    }

    /// Regression: an inline-asm template placeholder used to be rendered with
    /// Rust's Debug formatting, so `"ldr r0, ={stack_top}"` emitted
    /// `ldr r0, =Identifier("stack_top")` into the assembler, which fails with
    /// `unknown token in expression`.
    ///
    /// The anti-regression property is that the AST is never Debug-formatted
    /// into the template. The braces themselves are RETAINED (2026-09-01): a
    /// `{...}` in an asm template is an operand placeholder, so the marker must
    /// reach MIR lowering. `Identifier("stack_top")` must still never appear.
    #[test]
    fn test_asm_template_placeholder_renders_bare_identifier() {
        let asm = parse_first_asm("fn test():\n    asm volatile:\n        \"ldr r0, ={stack_top}\"\n");
        assert_eq!(asm.instructions.len(), 1);
        let instr = &asm.instructions[0];
        assert_eq!(instr, "ldr r0, ={stack_top}");
        assert!(
            !instr.contains("Identifier("),
            "Debug-formatted AST leaked into asm: {instr:?}"
        );
    }

    #[test]
    fn test_asm_template_placeholder_renders_integer_literal() {
        let asm = parse_first_asm("fn test():\n    asm volatile:\n        \"mov r0, #{7}\"\n");
        assert_eq!(asm.instructions, vec!["mov r0, #{7}".to_string()]);
    }

    /// Reproduce for
    /// `doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md`
    /// defect 2. RED before the fix: the block form flattened the operand
    /// placeholder to its bare token, so `src/lib/.../riscv/startup.spl`'s
    /// `"csrr {0}, mcause"` reached the riscv64 assembler as `csrr 0, mcause`
    /// ("invalid operand for instruction") and `src/os/kernel/arch/x86_32/
    /// paging.spl`'s `"invlpg [{addr}]"` as `invlpg [addr]` ("unknown
    /// operand"). Keeping the braces is what lets MIR bind them (`$N`) or the
    /// C sidecar skip them.
    #[test]
    fn test_asm_block_form_keeps_operand_placeholder_braces() {
        let asm = parse_first_asm(
            "fn test():\n    asm volatile:\n        \"csrr {0}, mcause\"\n        \"invlpg [{addr}]\"\n        \"call {3}\"\n",
        );
        assert_eq!(
            asm.instructions,
            vec![
                "csrr {0}, mcause".to_string(),
                "invlpg [{addr}]".to_string(),
                "call {3}".to_string(),
            ]
        );
    }

    /// The parenthesized form already preserved braces; the block form must now
    /// agree with it. A single contract, not two.
    #[test]
    fn test_asm_block_and_paren_forms_agree_on_placeholder_spelling() {
        let block = parse_first_asm("fn test():\n    asm volatile:\n        \"csrr {v}, mepc\"\n");
        let paren = parse_first_asm(
            "fn test(x: u64):\n    asm volatile(\n        \"csrr {v}, mepc\",\n        v = out(reg) x\n    )\n",
        );
        assert_eq!(block.instructions, paren.instructions);
        assert_eq!(block.instructions, vec!["csrr {v}, mepc".to_string()]);
    }

    /// A placeholder the assembler has no spelling for must be a loud parse
    /// error, never silently-emitted garbage.
    #[test]
    fn test_asm_template_placeholder_rejects_unsupported_operand() {
        let mut parser = crate::Parser::new("fn test():\n    asm volatile:\n        \"mov r0, {a + b}\"\n");
        let err = parser
            .parse()
            .err()
            .expect("expected parse error for unsupported asm placeholder");
        let msg = format!("{err:?}");
        assert!(
            msg.contains("unsupported operand in inline asm template placeholder"),
            "unexpected error: {msg}"
        );
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
    fn test_asm_volatile_braced_block() {
        let asm = parse_first_asm("fn test():\n    asm volatile {\n        mov r0, r1\n        add r0, r2\n    }\n");
        assert_eq!(asm.instructions, vec!["mov r0, r1", "add r0, r2"]);
        assert!(asm.volatile);
    }

    #[test]
    fn test_asm_braced_block_allows_commas_and_semicolons() {
        let asm = parse_first_asm("fn test():\n    asm {\n        \"nop\",\n        \"wfi\";\n    }\n");
        assert_eq!(asm.instructions, vec!["nop", "wfi"]);
    }

    #[test]
    fn test_asm_braced_raw_preserves_arm_immediate() {
        let asm = parse_first_asm("fn test():\n    asm volatile { bkpt #0 }\n");
        assert_eq!(asm.instructions, vec!["bkpt #0"]);
        assert!(asm.volatile);
    }

    #[test]
    fn test_asm_braced_raw_accepts_x86_arm_and_riscv_text() {
        let cases = [
            ("asm { cli }", "cli"),
            ("asm { mfence }", "mfence"),
            ("asm { cpsid i }", "cpsid i"),
            ("asm { wfi }", "wfi"),
            ("asm { fence rw, rw }", "fence rw, rw"),
            ("asm { csrr a0, mstatus }", "csrr a0, mstatus"),
        ];
        for (source, expected) in cases {
            let asm = parse_first_asm(&format!("fn test():\n    {source}\n"));
            assert_eq!(asm.instructions, vec![expected.to_string()]);
        }
    }

    #[test]
    fn test_asm_braced_raw_allows_placeholder_braces() {
        let asm = parse_first_asm("fn test():\n    asm { mov {out}, eax }\n");
        assert_eq!(asm.instructions, vec!["mov {out}, eax"]);
    }

    #[test]
    fn test_asm_braced_raw_allows_comment_like_hash_text_until_close() {
        let asm = parse_first_asm("fn test():\n    asm { svc #0 }\n");
        assert_eq!(asm.instructions, vec!["svc #0"]);
    }

    #[test]
    fn test_asm_volatile_paren_simple() {
        parse_succeeds("fn test():\n    asm volatile(\n        \"mov r0, r1\",\n        \"bkpt #0xAB\"\n    )\n");
    }

    #[test]
    fn test_asm_parenthesized_parses_with_legacy_warning() {
        let mut parser = crate::Parser::new("fn test():\n    asm(\"nop\")\n");
        parser.parse().expect("parse");
        assert!(parser
            .error_hints()
            .iter()
            .any(|hint| hint.message.contains("legacy inline asm syntax")));
    }

    #[test]
    fn test_asm_bare_string_parses_with_legacy_warning() {
        let mut parser = crate::Parser::new("fn test():\n    asm \"nop\"\n");
        parser.parse().expect("parse");
        assert!(parser
            .error_hints()
            .iter()
            .any(|hint| hint.message.contains("legacy inline asm syntax")));
    }

    #[test]
    fn test_asm_colon_string_parses_with_legacy_warning() {
        let mut parser = crate::Parser::new("fn test():\n    asm: \"nop\"\n");
        parser.parse().expect("parse");
        assert!(parser
            .error_hints()
            .iter()
            .any(|hint| hint.message.contains("legacy inline asm syntax")));
    }

    #[test]
    fn test_asm_volatile_paren_constraints() {
        let source = "fn test(op: u32, pp: u32):\n    var result: i64 = 0\n    asm volatile(\n        \"mov r0, {op}\",\n        \"bkpt #0xAB\",\n        op = in(reg) op,\n        params = in(reg) pp,\n        result = out(reg) result,\n        clobber_abi(\"C\")\n    )\n";
        parse_succeeds(source);
    }

    /// Reproduce for
    /// `doc/08_tracking/bug/riscv64_wm_closure_unbuildable_asm_clobber_string_2026-09-01.md`.
    /// RED before the fix: `expect_identifier()` in the `clobber` arm rejected
    /// the string with `expected identifier, found FString([Literal("memory")])`,
    /// which made every riscv64 entry reaching `os.kernel.arch.riscv64.display`
    /// unbuildable at discovery (`src/os/kernel/arch/riscv64/cpu.spl:150`).
    #[test]
    fn test_asm_volatile_paren_clobber_string_literal() {
        let asm = parse_first_asm(
            "fn test(v: u64):\n    asm volatile(\n        \"csrw sstatus, {operand}\",\n        operand = in(reg) v,\n        clobber(\"memory\")\n    )\n",
        );
        let clobbers: Vec<&str> = asm
            .constraints
            .iter()
            .filter(|c| matches!(c.kind, crate::ast::AsmConstraintKind::Clobber))
            .filter_map(|c| c.reg_class.as_deref())
            .collect();
        assert_eq!(clobbers, vec!["memory"]);
    }

    /// The x86 backend spells the same form with register names rather than the
    /// `memory` pseudo-register (`src/compiler/70.backend/backend/x86_asm.spl`).
    #[test]
    fn test_asm_volatile_paren_clobber_string_registers() {
        let asm = parse_first_asm(
            "fn test():\n    asm volatile(\n        \"cpuid\",\n        clobber(\"eax\"),\n        clobber(\"ebx\")\n    )\n",
        );
        let clobbers: Vec<&str> = asm
            .constraints
            .iter()
            .filter(|c| matches!(c.kind, crate::ast::AsmConstraintKind::Clobber))
            .filter_map(|c| c.reg_class.as_deref())
            .collect();
        assert_eq!(clobbers, vec!["eax", "ebx"]);
    }

    /// The bare-identifier spelling must keep working — this fix widens the
    /// grammar, it does not move it.
    #[test]
    fn test_asm_volatile_paren_clobber_bare_identifier_still_parses() {
        let asm = parse_first_asm(
            "fn test(v: u64):\n    asm volatile(\n        \"csrw sstatus, {operand}\",\n        operand = in(reg) v,\n        clobber(memory)\n    )\n",
        );
        assert!(asm
            .constraints
            .iter()
            .any(|c| matches!(c.kind, crate::ast::AsmConstraintKind::Clobber)
                && c.reg_class.as_deref() == Some("memory")));
    }

    #[test]
    fn test_asm_volatile_paren_options() {
        parse_succeeds(
            "fn test():\n    asm volatile(\n        \"csrsi mstatus, 0x8\",\n        options(nostack)\n    )\n",
        );
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
        parse_succeeds(
            "fn test(x: u64):\n    asm volatile(\n        \"csrc mip, {msie}\",\n        in(reg) x\n    )\n",
        );
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
