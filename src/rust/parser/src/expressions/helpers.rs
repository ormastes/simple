// Helper functions for expression parsing - lambdas, colon blocks, if expressions, and arguments

use crate::ast::{Argument, Expr, LambdaParam, MacroArg, MoveMode, Pattern};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_remaining_lambda_params(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        while self.check(&TokenKind::Comma) {
            self.advance();
            let name = self.expect_identifier()?;
            params.push(LambdaParam { name, ty: None });
        }
        Ok(())
    }

    /// Try to parse a colon-block as a trailing lambda.
    ///
    /// Syntax:
    /// ```text
    /// func arg:
    ///     statement1
    ///     statement2
    /// ```
    ///
    /// This is parsed as `func(arg, fn(): statement1; statement2)`.
    ///
    /// Returns `Some(lambda)` if we see `:` followed by newline and indent,
    /// `None` if this doesn't look like a colon-block.
    pub(super) fn try_parse_colon_block(&mut self) -> Result<Option<Expr>, ParseError> {
        // Must be at a colon
        if !self.check(&TokenKind::Colon) {
            return Ok(None);
        }

        // Peek ahead to see if this is a colon-block
        // We need: colon, newline, indent
        // Since we can't easily peek multiple tokens, we'll consume and check
        self.advance(); // consume ':'

        // Skip any newlines after the colon
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Must have indent for a block
        if !self.check(&TokenKind::Indent) {
            // Not a colon-block, but we already consumed the colon
            // This is an error state - colon without proper block
            return Err(ParseError::unexpected_token(
                "indented block after ':'",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }

        self.advance(); // consume Indent

        // Parse statements until dedent
        let mut statements = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
            // Skip newlines between statements
            while self.check(&TokenKind::Newline) {
                self.advance();
            }

            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                break;
            }

            let stmt = self.parse_item()?;
            statements.push(stmt);

            // Skip trailing newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume dedent if present
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        // Wrap statements in a DoBlock expression, then in a Lambda
        let block_expr = Expr::DoBlock(statements);

        Ok(Some(Expr::Lambda {
            params: vec![],
            body: Box::new(block_expr),
            move_mode: MoveMode::Copy,
            capture_all: false, // Do-block wrapping doesn't auto-capture
        }))
    }

    /// Parse an if/elif expression (shared logic)
    pub(crate) fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Support both inline and block-form syntax for then branch
        let then_branch = if self.check(&TokenKind::Newline) {
            // Block-form: parse as DoBlock expression
            self.advance(); // consume Newline
            self.expect(&TokenKind::Indent)?;

            let mut statements = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                // Skip empty lines
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) || self.is_at_end() {
                    break;
                }

                statements.push(self.parse_item()?);

                // Consume newline after statement if present
                if self.check(&TokenKind::Newline) {
                    self.advance();
                }
            }

            if self.check(&TokenKind::Dedent) {
                self.advance();
            }

            Expr::DoBlock(statements)
        } else {
            // Inline form: parse as expression
            self.parse_expression()?
        };

        let else_branch = if self.check(&TokenKind::Elif) {
            self.advance();
            Some(Box::new(self.parse_if_expr()?))
        } else if self.check(&TokenKind::Else) {
            self.advance();
            // Support both 'else if' and 'else:' syntax (matching statement parser)
            if self.check(&TokenKind::If) {
                // This is 'else if', treat it as elif
                self.advance(); // consume 'if'
                Some(Box::new(self.parse_if_expr()?))
            } else {
                self.expect(&TokenKind::Colon)?;

                // Support both inline and block-form syntax for else branch
                let else_expr = if self.check(&TokenKind::Newline) {
                    // Block-form: parse as DoBlock expression
                    self.advance(); // consume Newline
                    self.expect(&TokenKind::Indent)?;

                    let mut statements = Vec::new();
                    while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                        // Skip empty lines
                        while self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                        if self.check(&TokenKind::Dedent) || self.is_at_end() {
                            break;
                        }

                        statements.push(self.parse_item()?);

                        // Consume newline after statement if present
                        if self.check(&TokenKind::Newline) {
                            self.advance();
                        }
                    }

                    if self.check(&TokenKind::Dedent) {
                        self.advance();
                    }

                    Expr::DoBlock(statements)
                } else {
                    // Inline form: parse as expression
                    self.parse_expression()?
                };

                Some(Box::new(else_expr))
            }
        } else {
            None
        };
        Ok(Expr::If {
            let_pattern,
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch,
        })
    }

    pub(crate) fn parse_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut args = Vec::new();

        // Skip newlines and indent after opening paren (for multi-line argument lists)
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            self.advance();
        }

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            // Skip any stray whitespace tokens at the start of each argument
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
                self.advance();
            }
            if self.check(&TokenKind::RParen) {
                break;
            }

            // Check for named argument with '=' or ':' syntax
            // Also support keywords as named argument names (e.g., type="model", default=true)
            let mut name = None;
            let maybe_name = match &self.current.kind {
                TokenKind::Identifier { name: id, .. } => Some(id.clone()),
                // Allow keywords as named argument names
                TokenKind::Type => Some("type".to_string()),
                TokenKind::Default => Some("default".to_string()),
                TokenKind::Result => Some("result".to_string()),
                TokenKind::From => Some("from".to_string()),
                TokenKind::To => Some("to".to_string()),
                TokenKind::In => Some("in".to_string()),
                TokenKind::Is => Some("is".to_string()),
                TokenKind::As => Some("as".to_string()),
                TokenKind::Match => Some("match".to_string()),
                TokenKind::Use => Some("use".to_string()),
                _ => None,
            };
            if let Some(id_clone) = maybe_name {
                // Peek ahead for '=' or ':' without consuming the stream
                let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                    let tok = self.lexer.next_token();
                    self.pending_tokens.push_back(tok.clone());
                    tok
                });
                if next.kind == TokenKind::Assign {
                    name = Some(id_clone);
                    self.advance(); // consume identifier/keyword
                    self.expect(&TokenKind::Assign)?; // consume '='
                } else if next.kind == TokenKind::Colon {
                    // Support colon syntax: name: value
                    name = Some(id_clone);
                    self.advance(); // consume identifier/keyword
                    self.expect(&TokenKind::Colon)?; // consume ':'
                }
                // else leave current untouched; pending_tokens already holds the peeked token
            }

            let mut value = self.parse_expression()?;

            // Check for spread operator: args...
            // This enables spreading variadic parameters in function calls
            // Example: wrapper(args...) where args is a variadic parameter
            if self.check(&TokenKind::Ellipsis) {
                self.advance(); // consume ...
                value = Expr::Spread(Box::new(value));
            }

            args.push(Argument { name, value });

            // Skip newlines, indent, dedent after argument (for multi-line argument lists)
            while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
                self.advance();
            }

            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
                // Skip newlines, indent, dedent after comma
                while self.check(&TokenKind::Newline)
                    || self.check(&TokenKind::Indent)
                    || self.check(&TokenKind::Dedent)
                {
                    self.advance();
                }
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(args)
    }

    /// Parse macro invocation arguments: !(args) or !{args} or ![args]
    pub(crate) fn parse_macro_args(&mut self) -> Result<Vec<MacroArg>, ParseError> {
        // Macros can use (), {}, or [] for their arguments
        let (_open, close) = if self.check(&TokenKind::LParen) {
            (TokenKind::LParen, TokenKind::RParen)
        } else if self.check(&TokenKind::LBrace) {
            (TokenKind::LBrace, TokenKind::RBrace)
        } else if self.check(&TokenKind::LBracket) {
            (TokenKind::LBracket, TokenKind::RBracket)
        } else {
            return Err(ParseError::unexpected_token(
                "'(', '{', or '['",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.advance(); // consume opening delimiter
        let mut args = Vec::new();

        while !self.check(&close) {
            // Try to parse as expression
            let expr = self.parse_expression()?;
            args.push(MacroArg::Expr(expr));

            if !self.check(&close) {
                // Allow comma or semicolon as separator
                if self.check(&TokenKind::Comma) || self.check(&TokenKind::Semicolon) {
                    self.advance();
                }
            }
        }

        self.expect(&close)?;
        Ok(args)
    }

    /// Parse comprehension clause: `for pattern in iterable [if condition]`
    /// Returns (pattern, iterable, condition)
    pub(super) fn parse_comprehension_clause(&mut self) -> Result<(Pattern, Expr, Option<Box<Expr>>), ParseError> {
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expression()?;
        let condition = if self.check(&TokenKind::If) {
            self.advance();
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        Ok((pattern, iterable, condition))
    }

    /// Parse lambda body (params, colon, expression or block) with given move mode
    pub(super) fn parse_lambda_body(&mut self, move_mode: MoveMode) -> Result<Expr, ParseError> {
        let (params, capture_all) = self.parse_lambda_params()?;
        self.expect(&TokenKind::Colon)?;

        // Check if body is an indented block or inline expression
        let body = if self.check(&TokenKind::Newline) {
            // Enable forced indentation for lambda body (even inside brackets/parens)
            self.lexer.enable_forced_indentation();

            // Consume the newline
            self.advance();

            // Check if we have an indent (block body)
            if self.check(&TokenKind::Indent) {
                self.advance(); // consume Indent

                // Parse statements until dedent
                let mut statements = Vec::new();
                while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
                    // Skip newlines between statements
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }

                    if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                        break;
                    }

                    let stmt = self.parse_item()?;
                    statements.push(stmt);

                    // Skip trailing newlines
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                // Consume dedent if present
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }

                // Disable forced indentation after lambda body
                self.lexer.disable_forced_indentation();

                Expr::DoBlock(statements)
            } else {
                // Disable forced indentation - not a block
                self.lexer.disable_forced_indentation();

                // Just a newline, parse next expression
                self.parse_expression()?
            }
        } else {
            // Inline expression
            self.parse_expression()?
        };

        Ok(Expr::Lambda {
            params,
            body: Box::new(body),
            move_mode,
            capture_all,
        })
    }

    /// Create a slice expression with the given components
    #[allow(dead_code)]
    fn make_slice(receiver: Expr, start: Option<Expr>, end: Option<Expr>, step: Option<Box<Expr>>) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }
}
