//! Pattern parsing methods for Parser
//!
//! This module contains methods for parsing pattern expressions used in match statements.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::TokenKind;

use super::Parser;

impl<'a> Parser<'a> {
    // === Pattern Parsing ===

    pub(crate) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        // Parse the first pattern
        let first = self.parse_single_pattern()?;

        // Check for or patterns (pattern1 | pattern2 | ...)
        // Also handle multi-line patterns where | is at the start of a continuation line
        // The token sequence could be: Pipe directly, or Newline -> (Indent)? -> Pipe
        let has_pipe = self.check(&TokenKind::Pipe) || self.peek_past_whitespace_for_pipe();
        if has_pipe {
            let mut patterns = vec![first];
            // Skip any whitespace/newlines before the first |
            // NOTE: Use indent-aware skipping to pop indent_stack when consuming
            // Indent tokens during multi-line or-pattern continuation. This prevents
            // spurious Dedent tokens from being generated later.
            self.skip_whitespace_and_fix_indent();
            while self.check(&TokenKind::Pipe) {
                self.advance();
                // Skip whitespace/newlines between or-pattern alternatives
                self.skip_whitespace_and_fix_indent();
                patterns.push(self.parse_single_pattern()?);
                // Skip whitespace after each pattern alternative (for multi-line)
                self.skip_whitespace_and_fix_indent();
            }
            return Ok(Pattern::Or(patterns));
        }

        Ok(first)
    }

    /// Skip whitespace tokens (Newline, Indent, Dedent) while fixing indent_stack
    /// by popping entries for consumed Indent tokens. This prevents the lexer from
    /// generating spurious Dedent tokens later when or-patterns span multiple lines.
    fn skip_whitespace_and_fix_indent(&mut self) {
        while self.check(&TokenKind::Newline)
            || self.check(&TokenKind::Indent)
            || self.check(&TokenKind::Dedent)
        {
            if self.check(&TokenKind::Indent) {
                self.advance();
                self.lexer.indent_stack.pop();
            } else {
                self.advance();
            }
        }
    }

    /// Check if there's a Pipe token after whitespace tokens (Newline, Indent).
    /// If found, consumes the whitespace tokens so the caller sees Pipe as current.
    /// If not found, restores parser state completely.
    fn peek_past_whitespace_for_pipe(&mut self) -> bool {
        if !self.check(&TokenKind::Newline) {
            return false;
        }

        // Save parser state
        let saved_current = self.current.clone();
        let saved_previous = self.previous.clone();
        let saved_pending = self.pending_token.clone();

        // Track tokens obtained from the lexer/pending during look-ahead.
        // The first advance() consumes saved_current (Newline) and sets
        // self.current = pending_token.take() || lexer.next_token().
        // If saved_pending was Some, the first token comes from there and
        // should NOT be pushed to the lexer on restoration (it goes back as pending_token).
        // Subsequent tokens came from the lexer and must be pushed back.

        self.advance(); // consume Newline; current = saved_pending or lexer token
        let first_from_pending = saved_pending.is_some();

        // Collect tokens from further advances (these always come from lexer)
        let mut lexer_tokens = Vec::new();
        if !first_from_pending {
            lexer_tokens.push(self.current.clone());
        }

        let mut indent_count = 0;
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            if self.check(&TokenKind::Indent) {
                indent_count += 1;
            }
            self.advance();
            lexer_tokens.push(self.current.clone());
        }

        if self.check(&TokenKind::Pipe) {
            // Found pipe - leave parser in consumed state.
            // Pop indent_stack entries for consumed Indent tokens to prevent
            // spurious Dedent generation later.
            for _ in 0..indent_count {
                self.lexer.indent_stack.pop();
            }
            return true;
        }

        // Not found - restore state.
        // The final self.current and any self.pending_token came from the lexer.
        // We need to push them back so the lexer stream is intact.
        let leftover_pending = self.pending_token.take();

        // Push back in reverse order (lexer.pending_tokens is a stack, pop from end):
        // First push what comes last in the stream, then what comes first.
        if let Some(lp) = leftover_pending {
            self.lexer.pending_tokens.push(lp);
        }
        // lexer_tokens are in order [first, second, ..., last].
        // We want first to be popped first, so push in reverse.
        for tok in lexer_tokens.into_iter().rev() {
            self.lexer.pending_tokens.push(tok);
        }
        // If the first advance consumed from saved_pending, we already captured
        // subsequent tokens in lexer_tokens. The first token (from pending) goes
        // back as pending_token. But wait - if first_from_pending is true, the
        // second advance (in the while loop) produced a token that IS in lexer_tokens.
        // However, if first_from_pending is false, we included the first advance's
        // token in lexer_tokens already. Either way the streams are reconstructed.

        self.current = saved_current;
        self.previous = saved_previous;
        self.pending_token = saved_pending;
        false
    }

    pub(crate) fn parse_single_pattern(&mut self) -> Result<Pattern, ParseError> {
        match &self.current.kind.clone() {
            TokenKind::Underscore => {
                self.advance();
                Ok(Pattern::Wildcard)
            }
            TokenKind::Mut => {
                self.advance();
                let name = self.expect_identifier()?;
                Ok(Pattern::MutIdentifier(name))
            }
            TokenKind::Identifier(name) => {
                let name = name.clone();
                self.advance();

                // Check for struct pattern: Name { ... }
                if self.check(&TokenKind::LBrace) {
                    self.advance();
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RBrace) {
                        let field_name = self.expect_identifier()?;
                        let pattern = if self.check(&TokenKind::Colon) {
                            self.advance();
                            self.parse_pattern()?
                        } else {
                            Pattern::Identifier(field_name.clone())
                        };
                        fields.push((field_name, pattern));
                        if !self.check(&TokenKind::RBrace) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;
                    return Ok(Pattern::Struct { name, fields });
                }

                // Check for enum variant: Name::Variant or Name::Variant(...)
                // Also supports dot syntax: Name.Variant or Name.Variant(...)
                // Supports dotted module paths: core.traits.SeekFrom::Start(n)
                if self.check(&TokenKind::DoubleColon) || self.check(&TokenKind::Dot) {
                    // Accumulate dotted path segments
                    let mut path_segments = vec![name.clone()];
                    while self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) {
                        if self.check(&TokenKind::DoubleColon) {
                            self.advance();
                            let segment = self.expect_identifier()?;
                            path_segments.push(segment);
                            break; // :: always precedes the variant, stop
                        }
                        // Dot - continue accumulating path
                        self.advance();
                        let segment = self.expect_identifier()?;
                        path_segments.push(segment);
                    }
                    // The last segment is the variant, everything before is the enum name
                    let variant = path_segments.pop().unwrap_or_default();
                    let enum_name = if path_segments.is_empty() {
                        name.clone()
                    } else {
                        path_segments.join(".")
                    };
                    let payload = if self.check(&TokenKind::LParen) {
                        self.advance();
                        let mut patterns = Vec::new();
                        while !self.check(&TokenKind::RParen) {
                            patterns.push(self.parse_pattern()?);
                            if !self.check(&TokenKind::RParen) {
                                self.expect(&TokenKind::Comma)?;
                            }
                        }
                        self.expect(&TokenKind::RParen)?;
                        Some(patterns)
                    } else {
                        None
                    };
                    return Ok(Pattern::Enum {
                        name: enum_name,
                        variant,
                        payload,
                    });
                }

                // Check for unit enum variants without parentheses: None
                // These are builtin variants that don't take a payload
                if name == "None" {
                    return Ok(Pattern::Enum {
                        name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: None,
                    });
                }

                // Check for enum variant pattern with parentheses: VariantName(...)
                // This handles both builtin (Some, Ok, Err) and user-defined variants
                if self.check(&TokenKind::LParen) {
                    // Map builtin variants to their enum types
                    let (enum_name, variant) = match name.as_str() {
                        "Some" => ("Option".to_string(), "Some".to_string()),
                        "Ok" => ("Result".to_string(), "Ok".to_string()),
                        "Err" => ("Result".to_string(), "Err".to_string()),
                        // For user-defined variants, use "_" as placeholder enum name
                        // The interpreter will resolve based on the value being matched
                        _ => ("_".to_string(), name.clone()),
                    };
                    self.advance(); // consume LParen
                    let mut patterns = Vec::new();
                    while !self.check(&TokenKind::RParen) {
                        patterns.push(self.parse_pattern()?);
                        if !self.check(&TokenKind::RParen) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Pattern::Enum {
                        name: enum_name,
                        variant,
                        payload: Some(patterns),
                    });
                }

                // Check for typed pattern: name: Type (for union type discrimination)
                // This must be distinguished from struct field patterns, which are only
                // valid inside struct patterns (handled above in LBrace case)
                // Also must distinguish from match arm colon (case X:\n body)
                // When in_match_arm_pattern is true, colon is always the body delimiter
                if self.check(&TokenKind::Colon) && !self.in_match_arm_pattern {
                    let next = self
                        .pending_token
                        .clone()
                        .unwrap_or_else(|| self.lexer.next_token());
                    self.pending_token = Some(next.clone());
                    // Only treat as typed pattern if followed by a type-starting token
                    let is_type_start = matches!(
                        next.kind,
                        TokenKind::Identifier(_)
                            | TokenKind::LParen    // tuple type
                            | TokenKind::LBracket  // array type
                            | TokenKind::LBrace    // dict type
                            | TokenKind::Fn        // function type
                            | TokenKind::Self_     // Self type
                            | TokenKind::Ampersand // reference type &T
                            | TokenKind::Star      // pointer type *T
                            | TokenKind::Vec       // vec type
                    );
                    if is_type_start {
                        self.advance();
                        let ty = self.parse_type()?;
                        return Ok(Pattern::Typed {
                            pattern: Box::new(Pattern::Identifier(name)),
                            ty,
                        });
                    }
                }

                Ok(Pattern::Identifier(name))
            }
            TokenKind::Integer(_)
            | TokenKind::TypedInteger(_, _)
            | TokenKind::Float(_)
            | TokenKind::TypedFloat(_, _)
            | TokenKind::String(_)
            | TokenKind::RawString(_)
            | TokenKind::FString(_)
            | TokenKind::Bool(_)
            | TokenKind::Nil => {
                let expr = self.parse_primary()?;
                // Check for range pattern: start..end or start..=end
                if self.check(&TokenKind::DoubleDot) {
                    self.advance();
                    let end_expr = self.parse_primary()?;
                    return Ok(Pattern::Range {
                        start: Box::new(expr),
                        end: Box::new(end_expr),
                        inclusive: false,
                    });
                }
                if self.check(&TokenKind::DoubleDotEq) {
                    self.advance();
                    let end_expr = self.parse_primary()?;
                    return Ok(Pattern::Range {
                        start: Box::new(expr),
                        end: Box::new(end_expr),
                        inclusive: true,
                    });
                }
                Ok(Pattern::Literal(Box::new(expr)))
            }
            TokenKind::LParen => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RParen) {
                    let pat = self.parse_pattern()?;
                    // Handle named field patterns: (name: pattern, ...)
                    // If we just parsed an identifier and the next token is ':', treat it
                    // as a named binding and parse the actual binding pattern after ':'
                    if self.check(&TokenKind::Colon) {
                        self.advance(); // consume ':'
                        let binding_pattern = self.parse_pattern()?;
                        // Use the binding pattern (the name is just a field label)
                        patterns.push(binding_pattern);
                    } else {
                        patterns.push(pat);
                    }
                    if !self.check(&TokenKind::RParen) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(Pattern::Tuple(patterns))
            }
            TokenKind::LBracket => {
                self.advance();
                let mut patterns = Vec::new();
                while !self.check(&TokenKind::RBracket) {
                    if self.check(&TokenKind::Ellipsis) {
                        self.advance();
                        patterns.push(Pattern::Rest);
                    } else {
                        patterns.push(self.parse_pattern()?);
                    }
                    if !self.check(&TokenKind::RBracket) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBracket)?;
                Ok(Pattern::Array(patterns))
            }
            // Allow certain keywords to be used as identifier patterns
            TokenKind::Out => {
                self.advance();
                Ok(Pattern::Identifier("out".to_string()))
            }
            TokenKind::OutErr => {
                self.advance();
                Ok(Pattern::Identifier("out_err".to_string()))
            }
            TokenKind::Type => {
                self.advance();
                Ok(Pattern::Identifier("type".to_string()))
            }
            TokenKind::Result => {
                self.advance();
                Ok(Pattern::Identifier("result".to_string()))
            }
            TokenKind::To => {
                self.advance();
                Ok(Pattern::Identifier("to".to_string()))
            }
            TokenKind::NotTo => {
                self.advance();
                Ok(Pattern::Identifier("not_to".to_string()))
            }
            TokenKind::From => {
                self.advance();
                Ok(Pattern::Identifier("from".to_string()))
            }
            TokenKind::Loop => {
                self.advance();
                Ok(Pattern::Identifier("loop".to_string()))
            }
            TokenKind::Old => {
                self.advance();
                Ok(Pattern::Identifier("old".to_string()))
            }
            TokenKind::As => {
                self.advance();
                Ok(Pattern::Identifier("as".to_string()))
            }
            TokenKind::In => {
                self.advance();
                Ok(Pattern::Identifier("in".to_string()))
            }
            TokenKind::Var => {
                self.advance();
                Ok(Pattern::Identifier("var".to_string()))
            }
            TokenKind::Fn => {
                self.advance();
                Ok(Pattern::Identifier("fn".to_string()))
            }
            TokenKind::Let => {
                self.advance();
                Ok(Pattern::Identifier("let".to_string()))
            }
            TokenKind::Struct => {
                self.advance();
                Ok(Pattern::Identifier("struct".to_string()))
            }
            TokenKind::Class => {
                self.advance();
                Ok(Pattern::Identifier("class".to_string()))
            }
            TokenKind::Enum => {
                self.advance();
                Ok(Pattern::Identifier("enum".to_string()))
            }
            TokenKind::Trait => {
                self.advance();
                Ok(Pattern::Identifier("trait".to_string()))
            }
            TokenKind::Mixin => {
                self.advance();
                Ok(Pattern::Identifier("mixin".to_string()))
            }
            TokenKind::Impl => {
                self.advance();
                Ok(Pattern::Identifier("impl".to_string()))
            }
            TokenKind::Extern => {
                self.advance();
                Ok(Pattern::Identifier("extern".to_string()))
            }
            TokenKind::Static => {
                self.advance();
                Ok(Pattern::Identifier("static".to_string()))
            }
            TokenKind::Const => {
                self.advance();
                Ok(Pattern::Identifier("const".to_string()))
            }
            TokenKind::Self_ => {
                self.advance();
                Ok(Pattern::Identifier("self".to_string()))
            }
            TokenKind::Async => {
                self.advance();
                Ok(Pattern::Identifier("async".to_string()))
            }
            TokenKind::Await => {
                self.advance();
                Ok(Pattern::Identifier("await".to_string()))
            }
            TokenKind::Yield => {
                self.advance();
                Ok(Pattern::Identifier("yield".to_string()))
            }
            TokenKind::Spawn => {
                self.advance();
                Ok(Pattern::Identifier("spawn".to_string()))
            }
            TokenKind::Move => {
                self.advance();
                Ok(Pattern::Identifier("move".to_string()))
            }
            TokenKind::Union => {
                self.advance();
                Ok(Pattern::Identifier("union".to_string()))
            }
            TokenKind::Actor => {
                self.advance();
                Ok(Pattern::Identifier("actor".to_string()))
            }
            TokenKind::Macro => {
                self.advance();
                Ok(Pattern::Identifier("macro".to_string()))
            }
            TokenKind::With => {
                self.advance();
                Ok(Pattern::Identifier("with".to_string()))
            }
            TokenKind::Shared => {
                self.advance();
                Ok(Pattern::Identifier("shared".to_string()))
            }
            TokenKind::Context => {
                self.advance();
                Ok(Pattern::Identifier("context".to_string()))
            }
            TokenKind::Unit => {
                self.advance();
                Ok(Pattern::Identifier("unit".to_string()))
            }
            TokenKind::Alias => {
                self.advance();
                Ok(Pattern::Identifier("alias".to_string()))
            }
            TokenKind::New => {
                self.advance();
                Ok(Pattern::Identifier("new".to_string()))
            }
            TokenKind::Pub => {
                self.advance();
                Ok(Pattern::Identifier("pub".to_string()))
            }
            TokenKind::Priv => {
                self.advance();
                Ok(Pattern::Identifier("priv".to_string()))
            }
            TokenKind::Mod => {
                self.advance();
                Ok(Pattern::Identifier("mod".to_string()))
            }
            TokenKind::Super => {
                self.advance();
                Ok(Pattern::Identifier("super".to_string()))
            }
            TokenKind::Continue => {
                self.advance();
                Ok(Pattern::Identifier("continue".to_string()))
            }
            TokenKind::Break => {
                self.advance();
                Ok(Pattern::Identifier("break".to_string()))
            }
            TokenKind::Match => {
                self.advance();
                Ok(Pattern::Identifier("match".to_string()))
            }
            TokenKind::Return => {
                self.advance();
                Ok(Pattern::Identifier("return".to_string()))
            }
            TokenKind::If => {
                self.advance();
                Ok(Pattern::Identifier("if".to_string()))
            }
            TokenKind::While => {
                self.advance();
                Ok(Pattern::Identifier("while".to_string()))
            }
            TokenKind::For => {
                self.advance();
                Ok(Pattern::Identifier("for".to_string()))
            }
            TokenKind::Import => {
                self.advance();
                Ok(Pattern::Identifier("import".to_string()))
            }
            TokenKind::Export => {
                self.advance();
                Ok(Pattern::Identifier("export".to_string()))
            }
            TokenKind::Use => {
                self.advance();
                Ok(Pattern::Identifier("use".to_string()))
            }
            TokenKind::Vec => {
                self.advance();
                Ok(Pattern::Identifier("vec".to_string()))
            }
            TokenKind::Invariant => {
                self.advance();
                Ok(Pattern::Identifier("invariant".to_string()))
            }
            TokenKind::Requires => {
                self.advance();
                Ok(Pattern::Identifier("requires".to_string()))
            }
            TokenKind::Ensures => {
                self.advance();
                Ok(Pattern::Identifier("ensures".to_string()))
            }
            TokenKind::Gpu => {
                self.advance();
                Ok(Pattern::Identifier("gpu".to_string()))
            }
            TokenKind::Dyn => {
                self.advance();
                Ok(Pattern::Identifier("dyn".to_string()))
            }
            TokenKind::Bitfield => {
                self.advance();
                Ok(Pattern::Identifier("bitfield".to_string()))
            }
            TokenKind::Common => {
                self.advance();
                Ok(Pattern::Identifier("common".to_string()))
            }
            TokenKind::Me => {
                self.advance();
                Ok(Pattern::Identifier("me".to_string()))
            }
            TokenKind::Auto => {
                self.advance();
                Ok(Pattern::Identifier("auto".to_string()))
            }
            TokenKind::Case => {
                self.advance();
                Ok(Pattern::Identifier("case".to_string()))
            }
            TokenKind::Else => {
                self.advance();
                Ok(Pattern::Identifier("else".to_string()))
            }
            TokenKind::Elif => {
                self.advance();
                Ok(Pattern::Identifier("elif".to_string()))
            }
            // 'do' is treated as identifier in patterns since it's not a keyword
            // If Do variant existed: TokenKind::Do => { ... }
            _ if matches!(&self.current.kind, TokenKind::Identifier(s) if s == "do") => {
                self.advance();
                Ok(Pattern::Identifier("do".to_string()))
            }
            TokenKind::Minus => {
                // Negative literal pattern: -42
                self.advance();
                let inner = self.parse_single_pattern()?;
                match inner {
                    Pattern::Literal(expr) => {
                        Ok(Pattern::Literal(Box::new(Expr::Unary {
                            op: UnaryOp::Neg,
                            operand: expr,
                        })))
                    }
                    _ => Ok(Pattern::Identifier("-".to_string()))
                }
            }
            // Allow comparison operators as identifiers in patterns (used as variable names)
            TokenKind::Gt => {
                self.advance();
                Ok(Pattern::Identifier(">".to_string()))
            }
            TokenKind::Lt => {
                self.advance();
                Ok(Pattern::Identifier("<".to_string()))
            }
            TokenKind::PassDoNothing | TokenKind::PassDn | TokenKind::Pass => {
                self.advance();
                Ok(Pattern::Literal(Box::new(Expr::Nil)))
            }
            TokenKind::PassTodo => {
                self.advance();
                Ok(Pattern::Literal(Box::new(Expr::Nil)))
            }
            _ => Err(ParseError::unexpected_token(
                "pattern",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
