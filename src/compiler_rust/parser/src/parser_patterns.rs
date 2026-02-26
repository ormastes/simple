//! Pattern parsing methods for Parser
//!
//! This module contains methods for parsing pattern expressions used in match statements.

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    // === Pattern Parsing ===

    pub(crate) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        // Parse the first pattern
        let first = self.parse_single_pattern()?;

        // Check for or patterns (pattern1 | pattern2 | ...) or comma-separated
        // (pattern1, pattern2, ...). Both syntaxes produce Or patterns.
        //
        // Support multi-line patterns where pipe continues on next line:
        //   case 'a' | 'b'
        //      | 'c' | 'd':
        // Use peek to check if there's a pipe ahead (through newlines/indents)
        // Only consume those tokens if we actually find a pipe
        if self.check(&TokenKind::Pipe) || self.peek_through_newlines_and_indents_is(&TokenKind::Pipe) {
            // Skip to the pipe, tracking how many INDENTs we consume
            // These INDENTs will have matching DEDENTs that appear AFTER the arm body,
            // so we store the count in pattern_indent_count for parse_match_arm to handle
            self.pattern_indent_count += self.skip_newlines_and_indents_for_pattern();

            if self.check(&TokenKind::Pipe) {
                let mut patterns = vec![first];
                while self.check(&TokenKind::Pipe) {
                    self.advance();
                    // Skip whitespace after the pipe operator
                    self.pattern_indent_count += self.skip_newlines_and_indents_for_pattern();
                    patterns.push(self.parse_single_pattern()?);
                    // Check if there's another pipe (possibly on next line)
                    if self.peek_through_newlines_and_indents_is(&TokenKind::Pipe) {
                        self.pattern_indent_count += self.skip_newlines_and_indents_for_pattern();
                    }
                }
                // Note: DEDENTs are NOT consumed here - they appear after the arm body
                // and will be consumed by parse_match_arm
                return Ok(Pattern::Or(patterns));
            }
        }

        // Comma-separated or-patterns: `case Int(_), Float(_), Bool(_):`
        // The comma acts as pattern separator when followed by a pattern-start token
        // (not a colon, which would indicate named arguments).
        if self.check(&TokenKind::Comma) && self.is_comma_or_pattern_context() {
            let mut patterns = vec![first];
            while self.check(&TokenKind::Comma) {
                self.advance();
                patterns.push(self.parse_single_pattern()?);
            }
            return Ok(Pattern::Or(patterns));
        }

        Ok(first)
    }

    /// Check if comma is being used as an or-pattern separator in a match arm.
    /// Peek at the token after the comma to see if it starts a pattern.
    fn is_comma_or_pattern_context(&mut self) -> bool {
        // Peek at the token after the comma
        let next = self.peek_next();
        matches!(
            next.kind,
            TokenKind::Identifier { .. }
                | TokenKind::Underscore
                | TokenKind::Integer(_)
                | TokenKind::Float(_)
                | TokenKind::String(_)
                | TokenKind::RawString(_)
                | TokenKind::FString(_)
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Nil
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::Mut
                | TokenKind::Move
                | TokenKind::New
                | TokenKind::Old
                | TokenKind::Type
                | TokenKind::Val
                | TokenKind::Var
                | TokenKind::Minus
        )
    }

    /// Parse a keyword used as an identifier in pattern position.
    /// If followed by `(`, parse as an enum variant pattern with payload.
    /// If followed by `.` or `::`, parse as qualified enum variant.
    /// Otherwise return a simple identifier pattern.
    fn parse_keyword_as_pattern(&mut self, name: &str) -> Result<Pattern, ParseError> {
        self.advance(); // consume the keyword token

        // Check for enum variant with payload: Const(dest, _, _)
        if self.check(&TokenKind::LParen) {
            self.advance(); // consume '('
            let mut patterns = Vec::new();
            while !self.check(&TokenKind::RParen) {
                patterns.push(self.parse_pattern()?);
                if !self.check(&TokenKind::RParen) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RParen)?;
            return Ok(Pattern::Enum {
                name: "_".to_string(),
                variant: name.to_string(),
                payload: Some(patterns),
            });
        }

        // Check for qualified path: Name.Variant or Name::Variant
        if self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) {
            let mut path = vec![name.to_string()];
            while self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) {
                self.advance();
                path.push(self.expect_identifier()?);
            }
            let variant = path.pop().unwrap();
            let enum_name = path.join(".");
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

        Ok(Pattern::Identifier(name.to_string()))
    }

    /// Skip newlines and indents for pattern continuation.
    /// Returns the number of Indent tokens skipped.
    fn skip_newlines_and_indents_for_pattern(&mut self) -> usize {
        let mut indent_count = 0;
        while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent) {
            if matches!(self.current.kind, TokenKind::Indent) {
                indent_count += 1;
            }
            self.advance();
        }
        indent_count
    }

    fn parse_single_pattern(&mut self) -> Result<Pattern, ParseError> {
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
            TokenKind::Move => {
                self.advance();
                // Check if followed by an identifier - this is a move pattern (move name)
                if let TokenKind::Identifier { name, .. } = &self.current.kind {
                    let name = name.clone();
                    self.advance();
                    return Ok(Pattern::MoveIdentifier(name));
                }
                // Check for enum variant pattern: Move(...)
                if self.check(&TokenKind::LParen) {
                    self.advance();
                    let mut patterns = Vec::new();
                    while !self.check(&TokenKind::RParen) {
                        patterns.push(self.parse_pattern()?);
                        if !self.check(&TokenKind::RParen) {
                            self.expect(&TokenKind::Comma)?;
                        }
                    }
                    self.expect(&TokenKind::RParen)?;
                    return Ok(Pattern::Enum {
                        name: "_".to_string(),
                        variant: "Move".to_string(),
                        payload: Some(patterns),
                    });
                }
                // Just "move" by itself as identifier
                Ok(Pattern::Identifier("move".to_string()))
            }
            // Allow certain keywords as identifier patterns
            // These are keywords that are commonly used as variable names
            // Use parse_keyword_as_pattern to also handle enum variant form: Keyword(...)
            TokenKind::New => self.parse_keyword_as_pattern("new"),
            TokenKind::Old => self.parse_keyword_as_pattern("old"),
            TokenKind::Type => self.parse_keyword_as_pattern("type"),
            TokenKind::Examples => self.parse_keyword_as_pattern("examples"),
            TokenKind::From => self.parse_keyword_as_pattern("from"),
            TokenKind::Var => self.parse_keyword_as_pattern("var"),
            TokenKind::Exists => self.parse_keyword_as_pattern("exists"),
            TokenKind::Identifier { name, .. } => {
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
                // Now supports qualified paths: module.Type.Variant
                if self.check(&TokenKind::DoubleColon) || self.check(&TokenKind::Dot) {
                    // Build the full qualified path
                    let mut path = vec![name];

                    // Consume path segments (module.Type.Variant)
                    while self.check(&TokenKind::DoubleColon) || self.check(&TokenKind::Dot) {
                        self.advance();
                        path.push(self.expect_identifier()?);
                    }

                    // Last segment is the variant name
                    let variant = path.pop().unwrap();

                    // Join remaining path as the enum name
                    let enum_name = path.join(".");

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
                // Also distinguish from match arm separator: `case Active:` where the colon
                // is followed by Newline (block) or Indent, not a type.
                if self.check(&TokenKind::Colon) {
                    // Look ahead to see if what follows could be a type
                    // Types start with: Identifier, LParen, LBracket, Fn, Mut, Dyn, etc.
                    // If followed by Newline, Indent, or other non-type tokens, this colon
                    // is likely a match arm separator, not a typed pattern.
                    let is_type_start = self.peek_is_type_start();
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
                    patterns.push(self.parse_pattern()?);
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
            // Allow BDD/Gherkin keywords to be used as identifier patterns
            TokenKind::Context => {
                self.advance();
                Ok(Pattern::Identifier("context".to_string()))
            }
            TokenKind::Feature => {
                self.advance();
                Ok(Pattern::Identifier("feature".to_string()))
            }
            TokenKind::Scenario => {
                self.advance();
                Ok(Pattern::Identifier("scenario".to_string()))
            }
            TokenKind::Given => {
                self.advance();
                Ok(Pattern::Identifier("given".to_string()))
            }
            TokenKind::When => {
                self.advance();
                Ok(Pattern::Identifier("when".to_string()))
            }
            TokenKind::Then => {
                self.advance();
                Ok(Pattern::Identifier("then".to_string()))
            }
            // Allow 'common' as identifier pattern (stdlib directory name)
            TokenKind::Common => {
                self.advance();
                Ok(Pattern::Identifier("common".to_string()))
            }
            // Allow BDD/Gherkin 'outline' as identifier pattern
            TokenKind::Outline => {
                self.advance();
                Ok(Pattern::Identifier("outline".to_string()))
            }
            // Allow 'bounds' as identifier pattern
            TokenKind::Bounds => {
                self.advance();
                Ok(Pattern::Identifier("bounds".to_string()))
            }
            // Allow 'alias' as identifier pattern
            TokenKind::Alias => {
                self.advance();
                Ok(Pattern::Identifier("alias".to_string()))
            }
            // Allow 'default' as identifier pattern
            TokenKind::Default => {
                self.advance();
                Ok(Pattern::Identifier("default".to_string()))
            }
            // Allow additional keywords as identifier patterns (used as enum variant names)
            TokenKind::Loop => self.parse_keyword_as_pattern("Loop"),
            TokenKind::Vec => self.parse_keyword_as_pattern("Vec"),
            TokenKind::Unit => self.parse_keyword_as_pattern("Unit"),
            TokenKind::Sync => self.parse_keyword_as_pattern("Sync"),
            TokenKind::Async => self.parse_keyword_as_pattern("Async"),
            TokenKind::Slice => self.parse_keyword_as_pattern("Slice"),
            TokenKind::Tensor => self.parse_keyword_as_pattern("Tensor"),
            TokenKind::Grid => self.parse_keyword_as_pattern("Grid"),
            TokenKind::Flat => self.parse_keyword_as_pattern("Flat"),
            TokenKind::Shared => self.parse_keyword_as_pattern("Shared"),
            TokenKind::Gpu => self.parse_keyword_as_pattern("Gpu"),
            TokenKind::Extern => self.parse_keyword_as_pattern("Extern"),
            TokenKind::Static => self.parse_keyword_as_pattern("Static"),
            TokenKind::Const => self.parse_keyword_as_pattern("Const"),
            TokenKind::Super => self.parse_keyword_as_pattern("super"),
            TokenKind::Repr => self.parse_keyword_as_pattern("Repr"),
            TokenKind::Match => self.parse_keyword_as_pattern("Match"),
            TokenKind::Dyn => self.parse_keyword_as_pattern("Dyn"),
            TokenKind::Macro => self.parse_keyword_as_pattern("Macro"),
            TokenKind::Mixin => self.parse_keyword_as_pattern("Mixin"),
            TokenKind::Actor => self.parse_keyword_as_pattern("Actor"),
            TokenKind::Ghost => self.parse_keyword_as_pattern("Ghost"),
            TokenKind::Gen => self.parse_keyword_as_pattern("Gen"),
            TokenKind::Impl => self.parse_keyword_as_pattern("Impl"),
            TokenKind::Val => self.parse_keyword_as_pattern("Val"),
            TokenKind::Kernel => self.parse_keyword_as_pattern("Kernel"),
            TokenKind::Literal => self.parse_keyword_as_pattern("Literal"),
            // Low-level keywords usable as pattern identifiers
            TokenKind::Asm => self.parse_keyword_as_pattern("Asm"),
            TokenKind::Bitfield => self.parse_keyword_as_pattern("Bitfield"),
            TokenKind::Newtype => self.parse_keyword_as_pattern("Newtype"),
            TokenKind::Extend => self.parse_keyword_as_pattern("Extend"),
            TokenKind::Comptime => self.parse_keyword_as_pattern("Comptime"),
            // Type definition keywords usable as pattern identifiers
            TokenKind::Struct => self.parse_keyword_as_pattern("Struct"),
            TokenKind::Enum => self.parse_keyword_as_pattern("Enum"),
            TokenKind::Class => self.parse_keyword_as_pattern("Class"),
            TokenKind::Fn => self.parse_keyword_as_pattern("Fn"),
            TokenKind::Trait => self.parse_keyword_as_pattern("Trait"),
            // Additional keywords that appear as enum variant names
            TokenKind::Self_ => self.parse_keyword_as_pattern("Self"),
            TokenKind::Export => self.parse_keyword_as_pattern("Export"),
            // Negative literal patterns: -1, -2.5, etc.
            TokenKind::Minus => {
                self.advance(); // consume '-'
                match &self.current.kind {
                    TokenKind::Integer(n) => {
                        let neg = -n;
                        self.advance();
                        Ok(Pattern::Literal(Box::new(Expr::Integer(neg))))
                    }
                    TokenKind::Float(f) => {
                        let neg = -f;
                        self.advance();
                        Ok(Pattern::Literal(Box::new(Expr::Float(neg))))
                    }
                    _ => Err(ParseError::unexpected_token(
                        "number after '-' in pattern",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    )),
                }
            }
            _ => Err(ParseError::unexpected_token(
                "pattern",
                format!("{:?}", self.current.kind),
                self.current.span,
            )),
        }
    }
}
