//! Lean 4 block parsing
//!
//! Parses lean blocks for embedding Lean 4 formal verification code.
//!
//! Supported syntax:
//! - `lean { -- Lean 4 code }` - inline Lean code (parsed as expression/custom block)
//! - `lean import "path.lean"` - import external Lean file
//! - `lean import "path.lean" { -- extensions }` - import and extend
//! - `lean hint: "tactic"` - proof hint for Lean prover (VER-020)

use crate::ast::{CalcStep, CalcStmt, LeanBlock, Node, ProofHintStmt};
use crate::error::ParseError;
use crate::parser_impl::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    /// Parse a lean import block statement.
    ///
    /// Called when we've detected "lean" identifier followed by "import".
    /// Current token is the "lean" identifier.
    ///
    /// This handles:
    /// - `lean import "path"` - import only
    /// - `lean import "path" { code }` - import with extensions
    ///
    /// Note: `lean { code }` is handled as a CustomBlock expression by the lexer.
    pub(crate) fn parse_lean_import_block(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume "lean" identifier
        self.advance();

        // Consume 'import' keyword
        self.expect(&TokenKind::Import)?;

        // Expect string literal for import path
        let import_path = match &self.current.kind {
            TokenKind::String(s) | TokenKind::RawString(s) => {
                let path = s.clone();
                self.advance();
                path
            }
            TokenKind::FString(parts) => {
                // Extract literal parts only (no interpolation in import paths)
                let mut path = String::new();
                for part in parts {
                    match part {
                        crate::token::FStringToken::Literal(s) => path.push_str(s),
                        crate::token::FStringToken::Expr(_) => {
                            return Err(ParseError::syntax_error_with_span(
                                "import path cannot contain interpolated expressions",
                                self.current.span,
                            ));
                        }
                    }
                }
                self.advance();
                path
            }
            _ => {
                return Err(ParseError::syntax_error_with_span(
                    "expected string literal for import path",
                    self.current.span,
                ));
            }
        };

        // Check for optional inline code block: lean import "path" { code }
        let code = if let TokenKind::CustomBlock { kind, payload } = &self.current.kind {
            if kind == "lean" {
                let c = payload.clone();
                self.advance();
                c
            } else {
                String::new()
            }
        } else {
            String::new()
        };

        let end_span = self.previous.span;
        let span = Span::new(start_span.start, end_span.end, start_span.line, start_span.column);

        Ok(Node::LeanBlock(LeanBlock {
            span,
            import_path: Some(import_path),
            code,
        }))
    }

    /// Parse a lean custom block expression into a LeanBlock node.
    ///
    /// This converts `lean{...}` custom block expressions to LeanBlock statements.
    pub(crate) fn parse_lean_custom_block_as_node(&mut self) -> Result<Node, ParseError> {
        let span = self.current.span;

        if let TokenKind::CustomBlock { kind, payload } = &self.current.kind {
            if kind == "lean" {
                let code = payload.clone();
                self.advance();

                return Ok(Node::LeanBlock(LeanBlock {
                    span,
                    import_path: None,
                    code,
                }));
            }
        }

        Err(ParseError::syntax_error_with_span(
            "expected lean{...} custom block",
            self.current.span,
        ))
    }

    /// Parse a lean hint statement for proof tactics (VER-020).
    ///
    /// Syntax: `lean hint: "tactic string"`
    ///
    /// Current token is "lean" identifier. Peeks ahead to see "hint".
    pub(crate) fn parse_lean_hint(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume "lean" identifier
        self.advance();

        // Consume "hint" identifier
        if !matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "hint") {
            return Err(ParseError::syntax_error_with_span(
                "expected 'hint' after 'lean'",
                self.current.span,
            ));
        }
        self.advance();

        // Expect colon
        self.expect(&TokenKind::Colon)?;

        // Expect string literal with tactic
        let hint = match &self.current.kind {
            TokenKind::String(s) | TokenKind::RawString(s) => {
                let h = s.clone();
                self.advance();
                h
            }
            _ => {
                return Err(ParseError::syntax_error_with_span(
                    "expected string literal for lean hint tactic",
                    self.current.span,
                ));
            }
        };

        let end_span = self.previous.span;
        let span = Span::new(start_span.start, end_span.end, start_span.line, start_span.column);

        Ok(Node::ProofHint(ProofHintStmt { span, hint }))
    }

    /// Parse a calculational proof block (VER-021).
    ///
    /// Syntax:
    /// ```simple
    /// calc:
    ///     sum(0..=n)
    ///     == sum(0..n) + n        by: "definition"
    ///     == (n-1)*n/2 + n        by: "induction hypothesis"
    ///     == n * (n + 1) / 2      by: "factor"
    /// ```
    ///
    /// Current token is `calc` identifier.
    pub(crate) fn parse_calc(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Consume "calc" identifier (not a keyword to avoid conflicts with variable names)
        if !matches!(&self.current.kind, TokenKind::Identifier { name, .. } if name == "calc") {
            return Err(ParseError::syntax_error_with_span("expected 'calc'", self.current.span));
        }
        self.advance();

        // Expect colon
        self.expect(&TokenKind::Colon)?;

        // Expect newline and indent for block
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut steps = Vec::new();

        // Parse first expression (the starting term - no leading ==)
        let first_expr_span = self.current.span;
        let first_expr = self.parse_expression()?;

        // Check for optional justification on first line
        let first_justification = self.parse_calc_justification()?;

        steps.push(CalcStep {
            span: Span::new(
                first_expr_span.start,
                self.previous.span.end,
                first_expr_span.line,
                first_expr_span.column,
            ),
            expr: first_expr,
            justification: first_justification,
        });

        // Expect newline after first expression
        if self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Parse subsequent steps: == expr (optional by: "justification")
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            let step_span = self.current.span;

            // Each subsequent step starts with ==
            if !self.check(&TokenKind::Eq) {
                break;
            }
            self.advance(); // consume ==

            // Parse the expression
            let expr = self.parse_expression()?;

            // Check for optional justification: by: "reason"
            let justification = self.parse_calc_justification()?;

            steps.push(CalcStep {
                span: Span::new(
                    step_span.start,
                    self.previous.span.end,
                    step_span.line,
                    step_span.column,
                ),
                expr,
                justification,
            });

            // Expect newline between steps (or dedent at end)
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Expect dedent at end of calc block
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        let end_span = self.previous.span;
        let span = Span::new(start_span.start, end_span.end, start_span.line, start_span.column);

        Ok(Node::Calc(CalcStmt { span, steps }))
    }

    /// Parse optional justification: `by: "reason"`
    fn parse_calc_justification(&mut self) -> Result<Option<String>, ParseError> {
        // Check for "by" identifier followed by colon
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            if name == "by" {
                self.advance(); // consume "by"
                self.expect(&TokenKind::Colon)?;

                // Expect string literal
                match &self.current.kind {
                    TokenKind::String(s) | TokenKind::RawString(s) => {
                        let justification = s.clone();
                        self.advance();
                        return Ok(Some(justification));
                    }
                    _ => {
                        return Err(ParseError::syntax_error_with_span(
                            "expected string literal for calc justification",
                            self.current.span,
                        ));
                    }
                }
            }
        }
        Ok(None)
    }
}
