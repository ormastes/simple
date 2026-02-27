// Helper functions for expression parsing - lambdas, colon blocks, if expressions, and arguments

use crate::ast::{Argument, Expr, LambdaParam, MacroArg, MoveMode, Pattern};
use crate::Span;
use crate::error::ParseError;
use crate::expressions::placeholder::transform_placeholder_lambda;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(super) fn parse_remaining_lambda_params(&mut self, params: &mut Vec<LambdaParam>) -> Result<(), ParseError> {
        while self.check(&TokenKind::Comma) {
            self.advance();
            // Support wildcard parameter: \x, _: or |x, _|
            let name = if self.check(&TokenKind::Underscore) {
                self.advance();
                "_".to_string()
            } else {
                self.expect_identifier()?
            };
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
            // Check for empty block: colon followed by dedent (comment-only or empty body)
            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                // Empty colon block — return empty lambda
                return Ok(Some(Expr::Lambda {
                    params: vec![],
                    body: Box::new(Expr::Tuple(vec![])),
                    move_mode: MoveMode::Copy,
                    capture_all: false,
                }));
            }
            // Not a colon-block, but we already consumed the colon
            // This is an error state - colon without proper block
            return Err(ParseError::unexpected_token(
                "indented block after ':'",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        }

        self.advance(); // consume Indent

        // Check for immediately empty block (Indent followed by Dedent)
        if self.check(&TokenKind::Dedent) {
            self.advance(); // consume Dedent
            return Ok(Some(Expr::Lambda {
                params: vec![],
                body: Box::new(Expr::Tuple(vec![])),
                move_mode: MoveMode::Copy,
                capture_all: false,
            }));
        }

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

    /// Parse a curly-brace delimited block as an expression: { stmt; stmt; expr }
    fn parse_brace_block_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect(&TokenKind::LBrace)?;
        // Skip newlines after opening brace
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
            self.advance();
        }
        if self.check(&TokenKind::RBrace) {
            self.advance();
            return Ok(Expr::DoBlock(Vec::new()));
        }
        // For simple single-expression blocks like { "alive" }
        let expr = self.parse_expression()?;
        // Skip newlines before closing brace
        while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) || self.check(&TokenKind::Dedent) {
            self.advance();
        }
        self.expect(&TokenKind::RBrace)?;
        Ok(expr)
    }

    /// Parse an if/elif expression (shared logic)
    pub(crate) fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        // Temporarily disable brace postfix to prevent { body } from being consumed as method call
        let old_no_brace = self.no_brace_postfix;
        self.no_brace_postfix = true;
        let (let_pattern, condition) = self.parse_optional_let_pattern()?;
        self.no_brace_postfix = old_no_brace;

        // Support colon, 'then', or curly brace syntax:
        //   if cond: body
        //   if cond then body else other
        //   if cond { body } else { other }
        let use_braces = self.check(&TokenKind::LBrace);
        if !use_braces {
            // Accept either ':' or 'then' keyword
            if self.check(&TokenKind::Then) {
                self.advance(); // consume 'then'
            } else {
                self.expect(&TokenKind::Colon)?;
            }
        }

        // Support both inline and block-form syntax for then branch
        let then_branch = if use_braces {
            // Curly brace form: if cond { body } else { body }
            self.parse_brace_block_expr()?
        } else if self.check(&TokenKind::Newline) {
            // Block-form: parse as DoBlock expression
            self.advance(); // consume Newline

            // Empty then-branch: `if cond:\nelse: ...` or `if cond:\nelif ...:`
            if self.check(&TokenKind::Else) || self.check(&TokenKind::Elif) {
                Expr::Tuple(vec![]) // unit value
            } else {
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
            } // close else for empty-then-branch check
        } else if self.check(&TokenKind::Return)
            || self.check(&TokenKind::Break)
            || self.check(&TokenKind::Continue)
        {
            // Diverging statement in then branch: `if cond: return val`
            let stmt = self.parse_item()?;
            Expr::DoBlock(vec![stmt])
        } else {
            // Inline form: parse as expression
            self.parse_expression()?
        };

        // Peek through newlines/indents to check for elif/else continuation.
        // Handles multi-line if-expressions like:
        //   val kind = if cond: ValueA
        //              else: ValueB
        // Only consume newlines/indents if elif/else actually follows,
        // otherwise leave them for the outer parser.
        // Track indent count to consume matching Dedent tokens after parsing else.
        let mut continuation_indents = 0;
        if self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
            let has_elif_or_else = self.peek_through_newlines_and_indents_is(&TokenKind::Elif)
                || self.peek_through_newlines_and_indents_is(&TokenKind::Else);
            if has_elif_or_else {
                while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                    if self.check(&TokenKind::Indent) {
                        continuation_indents += 1;
                    }
                    self.advance();
                }
            }
        }

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
            } else if self.check(&TokenKind::LBrace) {
                // Curly brace form: else { body }
                Some(Box::new(self.parse_brace_block_expr()?))
            } else {
                // Accept ':' after else, or skip it for 'then...else...' form
                // (if then was used instead of colon, else doesn't need colon either)
                if self.check(&TokenKind::Colon) {
                    self.advance();
                }

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
                } else if self.check(&TokenKind::Return)
                    || self.check(&TokenKind::Break)
                    || self.check(&TokenKind::Continue)
                {
                    // Diverging statement in else branch: `else: return nil`
                    let stmt = self.parse_item()?;
                    Expr::DoBlock(vec![stmt])
                } else {
                    // Inline form: parse as expression
                    self.parse_expression()?
                };

                Some(Box::new(else_expr))
            }
        } else {
            None
        };

        // Consume Dedent tokens matching the Indent tokens we consumed
        // when peeking through for continuation elif/else.
        // After parsing the else-branch, the token stream has: Newline Dedent
        // We need to consume both to balance the Indent we consumed earlier.
        // If we don't, the block parser will see the Dedent and think the
        // block ended prematurely.
        if continuation_indents > 0 {
            for _ in 0..continuation_indents {
                // Skip the trailing Newline to reach the Dedent
                if self.check(&TokenKind::Newline) {
                    // Peek to see if Dedent follows
                    let next = self.peek_next();
                    if matches!(next.kind, TokenKind::Dedent) {
                        self.advance(); // consume Newline
                        self.advance(); // consume Dedent
                    }
                } else if self.check(&TokenKind::Dedent) {
                    self.advance(); // consume Dedent
                }
            }
        }

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

        // Skip newlines, indent, and doc comments after opening paren (for multi-line argument lists)
        while self.check(&TokenKind::Newline)
            || self.check(&TokenKind::Indent)
            || matches!(&self.current.kind, TokenKind::DocComment(_))
        {
            self.advance();
        }

        while !self.check(&TokenKind::RParen) && !self.check(&TokenKind::Eof) {
            // Skip any stray whitespace and doc comment tokens at the start of each argument
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
                || matches!(&self.current.kind, TokenKind::DocComment(_))
            {
                self.advance();
            }
            if self.check(&TokenKind::RParen) {
                break;
            }

            // Record start position for span
            let arg_start = self.current.span;

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
                TokenKind::Alias => Some("alias".to_string()),
                TokenKind::Bounds => Some("bounds".to_string()),
                TokenKind::Outline => Some("outline".to_string()),
                TokenKind::By => Some("by".to_string()),
                TokenKind::Into => Some("into".to_string()),
                TokenKind::Onto => Some("onto".to_string()),
                TokenKind::With => Some("with".to_string()),
                // Additional keywords used as named argument names in Simple source
                TokenKind::Loop => Some("loop".to_string()),
                TokenKind::Unit => Some("unit".to_string()),
                TokenKind::Sync => Some("sync".to_string()),
                TokenKind::Async => Some("async".to_string()),
                TokenKind::Kernel => Some("kernel".to_string()),
                TokenKind::Val => Some("val".to_string()),
                TokenKind::Literal => Some("literal".to_string()),
                TokenKind::Repr => Some("repr".to_string()),
                TokenKind::Extern => Some("extern".to_string()),
                TokenKind::Static => Some("static".to_string()),
                TokenKind::Const => Some("const".to_string()),
                TokenKind::Shared => Some("shared".to_string()),
                TokenKind::Dyn => Some("dyn".to_string()),
                TokenKind::Macro => Some("macro".to_string()),
                TokenKind::Mixin => Some("mixin".to_string()),
                TokenKind::Actor => Some("actor".to_string()),
                TokenKind::Ghost => Some("ghost".to_string()),
                TokenKind::Gen => Some("gen".to_string()),
                TokenKind::Impl => Some("impl".to_string()),
                TokenKind::Gpu => Some("gpu".to_string()),
                TokenKind::Vec => Some("vec".to_string()),
                TokenKind::Context => Some("context".to_string()),
                TokenKind::Feature => Some("feature".to_string()),
                TokenKind::Scenario => Some("scenario".to_string()),
                TokenKind::Given => Some("given".to_string()),
                TokenKind::When => Some("when".to_string()),
                TokenKind::Then => Some("then".to_string()),
                TokenKind::On => Some("on".to_string()),
                TokenKind::Bind => Some("bind".to_string()),
                TokenKind::New => Some("new".to_string()),
                TokenKind::Old => Some("old".to_string()),
                TokenKind::Out => Some("out".to_string()),
                TokenKind::Var => Some("var".to_string()),
                _ => None,
            };
            if let Some(id_clone) = maybe_name {
                // Peek ahead for '=' or ':' without consuming the stream
                let next = self.peek_next();
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

            // Transform placeholder lambda syntax: _ * 2 -> \__p0: __p0 * 2
            // Count and replace all _ identifiers with unique parameters
            value = transform_placeholder_lambda(value);

            // Create span from start to current position
            let arg_end = self.previous.span;
            let arg_span = Span::new(arg_start.start, arg_end.end, arg_start.line, arg_start.column);

            // Check for call-site label keyword after value (e.g., `src to,`)
            let label = if self.check(&TokenKind::To) {
                self.advance();
                Some("to".to_string())
            } else if self.check(&TokenKind::From) {
                self.advance();
                Some("from".to_string())
            } else if self.check(&TokenKind::By) {
                self.advance();
                Some("by".to_string())
            } else if self.check(&TokenKind::Into) {
                self.advance();
                Some("into".to_string())
            } else if self.check(&TokenKind::Onto) {
                self.advance();
                Some("onto".to_string())
            } else if self.check(&TokenKind::With) {
                self.advance();
                Some("with".to_string())
            } else {
                None
            };

            args.push(Argument {
                name,
                value,
                span: arg_span,
                label,
            });

            // Skip newlines, indent, dedent, and doc comments after argument (for multi-line argument lists)
            // DocComment tokens may appear from desugared code (e.g., "DESUGARED: field: nil")
            while self.check(&TokenKind::Newline)
                || self.check(&TokenKind::Indent)
                || self.check(&TokenKind::Dedent)
                || matches!(&self.current.kind, TokenKind::DocComment(_))
            {
                self.advance();
            }

            if !self.check(&TokenKind::RParen) {
                // Check if we found another identifier (possibly starting a named argument)
                // This catches: func(a: 1 b: 2) where comma is missing
                let is_likely_named_arg = matches!(
                    &self.current.kind,
                    TokenKind::Identifier { .. }
                        | TokenKind::Type
                        | TokenKind::Default
                        | TokenKind::Result
                        | TokenKind::From
                        | TokenKind::To
                        | TokenKind::In
                        | TokenKind::Is
                        | TokenKind::As
                        | TokenKind::Match
                        | TokenKind::Use
                        | TokenKind::Alias
                        | TokenKind::Bounds
                        | TokenKind::By
                        | TokenKind::Into
                        | TokenKind::Onto
                        | TokenKind::With
                        | TokenKind::Loop
                        | TokenKind::Unit
                        | TokenKind::Sync
                        | TokenKind::Async
                        | TokenKind::Kernel
                        | TokenKind::Val
                        | TokenKind::Literal
                        | TokenKind::Repr
                        | TokenKind::Extern
                        | TokenKind::Static
                        | TokenKind::Const
                        | TokenKind::Shared
                        | TokenKind::Dyn
                        | TokenKind::Macro
                        | TokenKind::Mixin
                        | TokenKind::Actor
                        | TokenKind::Ghost
                        | TokenKind::Gen
                        | TokenKind::Impl
                        | TokenKind::Gpu
                        | TokenKind::Vec
                        | TokenKind::Context
                        | TokenKind::Feature
                        | TokenKind::Scenario
                        | TokenKind::Given
                        | TokenKind::When
                        | TokenKind::Then
                        | TokenKind::On
                        | TokenKind::Bind
                        | TokenKind::New
                        | TokenKind::Old
                        | TokenKind::Out
                        | TokenKind::Var
                );

                if is_likely_named_arg {
                    // Peek ahead to see if there's a colon or equals after this identifier
                    let next = self.pending_tokens.front().cloned().unwrap_or_else(|| {
                        let tok = self.lexer.next_token();
                        self.pending_tokens.push_back(tok.clone());
                        tok
                    });

                    if matches!(next.kind, TokenKind::Colon | TokenKind::Assign) {
                        // This is definitely a missing comma before a named argument
                        return Err(ParseError::contextual_error_with_help(
                            "function arguments",
                            format!(
                                "expected comma before argument '{}', found identifier",
                                self.current.lexeme
                            ),
                            self.current.span,
                            Some(format!("Insert comma before '{}'", self.current.lexeme)),
                            "Missing comma between function arguments. Use: func(a: 1, b: 2)",
                        ));
                    }
                }

                self.expect_with_context(
                    &TokenKind::Comma,
                    "function arguments",
                    Some("Insert comma between arguments".to_string()),
                )?;
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
        // Enable forced indentation BEFORE consuming colon, so the newline after colon is preserved
        // This handles lambda expressions inside function call arguments where newlines would be suppressed
        self.lexer.enable_forced_indentation();
        self.expect(&TokenKind::Colon)?;

        // Check if body is an indented block or inline expression
        let body = if self.check(&TokenKind::Newline) {
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

                    // Stop at closing brackets when the lambda body is inside a function call.
                    // Example: items.filter(\d:\n    not done.contains(d)).len()
                    // The `)` that closes .filter(...) terminates the lambda body.
                    if matches!(self.current.kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                        break;
                    }

                    let stmt = self.parse_item()?;
                    statements.push(stmt);

                    // Skip trailing newlines
                    while self.check(&TokenKind::Newline) {
                        self.advance();
                    }
                }

                // Consume dedent if present.
                // If we broke at a closing bracket (RParen etc.), the dedent may come
                // later as the bracket closes. Pop the lexer's indent stack to stay in sync.
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                } else if matches!(self.current.kind, TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace) {
                    // Lambda body ended at a closing bracket without a Dedent.
                    // Pop the indent stack to keep it in sync.
                    self.lexer.pop_indent();
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
        } else if self.check(&TokenKind::LBrace) && self.peek_brace_is_lambda_block() {
            // Brace-delimited block body: \x: { var acc = ...; for item in data: ... }
            // Enable forced indentation BEFORE consuming { so the lexer generates
            // proper Newline/Indent/Dedent tokens inside the brace block.
            // bracket_depth is already at inside-brace level (lexer incremented when scanning {).
            self.lexer.enable_forced_indentation();
            self.advance(); // consume { — next token from lexer has proper indentation
            // Skip newlines/indents inside brace block
            while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent) {
                self.advance();
            }
            let mut statements = Vec::new();
            while !self.check(&TokenKind::RBrace) && !self.check(&TokenKind::Eof) {
                while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent) {
                    self.advance();
                }
                if self.check(&TokenKind::RBrace) || self.check(&TokenKind::Eof) {
                    break;
                }
                let stmt = self.parse_item()?;
                statements.push(stmt);
                while matches!(self.current.kind, TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent) {
                    self.advance();
                }
            }
            // Disable inner forced indentation before consuming }
            self.lexer.disable_forced_indentation();
            self.expect(&TokenKind::RBrace)?;
            // Disable outer forced indentation (from before the colon at line 648)
            self.lexer.disable_forced_indentation();
            Expr::DoBlock(statements)
        } else {
            // Inline expression - disable forced indentation after parsing
            let expr = self.parse_expression()?;
            self.lexer.disable_forced_indentation();
            expr
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
