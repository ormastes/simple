//! Lean 4 block parsing
//!
//! Parses lean blocks for embedding Lean 4 formal verification code.
//!
//! Supported syntax:
//! - `lean { -- Lean 4 code }` - inline Lean code (parsed as expression/custom block)
//! - `lean import "path.lean"` - import external Lean file
//! - `lean import "path.lean" { -- extensions }` - import and extend

use crate::ast::{LeanBlock, Node};
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
}
