use crate::ast::{Argument, AssignOp, AssignmentStmt, Expr, Node};
use crate::error::ParseError;
use crate::parser_impl::core::{Parser, ParserMode};
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    pub(crate) fn parse_expression_or_assignment(&mut self) -> Result<Node, ParseError> {
        let expr = self.parse_expression()?;

        // Check for assignment
        let assign_op = match &self.current.kind {
            TokenKind::Assign => Some(AssignOp::Assign),
            TokenKind::PlusAssign => Some(AssignOp::AddAssign),
            TokenKind::MinusAssign => Some(AssignOp::SubAssign),
            TokenKind::StarAssign => Some(AssignOp::MulAssign),
            TokenKind::SlashAssign => Some(AssignOp::DivAssign),
            TokenKind::TildeAssign => Some(AssignOp::SuspendAssign),
            _ => None,
        };

        if let Some(op) = assign_op {
            let span = self.current.span;
            self.advance();
            let value = self.parse_expression()?;
            Ok(Node::Assignment(AssignmentStmt {
                span,
                target: expr,
                op,
                value,
            }))
        } else {
            // Parse the expression with potential no-paren calls
            let expr = self.parse_with_no_paren_calls(expr)?;

            // Check for infix keywords (to, not_to) and convert to method calls
            // e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
            let expr = self.parse_infix_keywords(expr)?;

            Ok(Node::Expression(expr))
        }
    }

    /// Parse no-paren calls on an expression
    fn parse_with_no_paren_calls(&mut self, expr: Expr) -> Result<Expr, ParseError> {
        // Check for colon-block on plain identifier FIRST
        // e.g., `given:` or `describe:` without arguments
        // This must come before can_start_argument() check because colon is in that list
        if self.is_callable_expr(&expr) && self.is_at_colon_block() {
            if let Some(block_lambda) = self.try_parse_colon_block()? {
                let args = vec![Argument {
                    name: None,
                    value: block_lambda,
                }];
                return Ok(self.make_call_expr(expr, args));
            }
        }
        // Check for no-parentheses call at statement level
        // Only for identifiers or field access followed by argument-starting tokens
        else if self.is_callable_expr(&expr) && self.can_start_argument() {
            // In strict mode, only allow outermost no-paren call
            // If we're already inside a no-paren call (depth > 0), require parentheses
            if self.mode == ParserMode::Strict && self.no_paren_depth > 0 {
                return Ok(expr);
            }

            // Track depth for strict mode
            self.no_paren_depth += 1;
            let mut args = self.parse_no_paren_arguments()?;
            self.no_paren_depth -= 1;

            // Check for trailing lambda: func arg \x: body
            if self.check(&TokenKind::Backslash) {
                let trailing_lambda = self.parse_trailing_lambda()?;
                args.push(Argument {
                    name: None,
                    value: trailing_lambda,
                });
            }
            // Check for trailing colon-block: func arg:
            //     body
            // This becomes: func(arg, fn(): body)
            else if self.check(&TokenKind::Colon) {
                if let Some(block_lambda) = self.try_parse_colon_block()? {
                    args.push(Argument {
                        name: None,
                        value: block_lambda,
                    });
                }
            }

            if !args.is_empty() {
                return Ok(self.make_call_expr(expr, args));
            }
        }
        Ok(expr)
    }

    /// Parse infix keywords (to, not_to) as method calls
    /// e.g., `expect 5 to eq 5` → `expect(5).to(eq(5))`
    fn parse_infix_keywords(&mut self, mut expr: Expr) -> Result<Expr, ParseError> {
        loop {
            let method_name = match &self.current.kind {
                TokenKind::To => "to",
                TokenKind::NotTo => "not_to",
                _ => break,
            };

            self.advance(); // consume `to` or `not_to`

            // Parse the argument expression (with no-paren calls allowed)
            let arg_expr = self.parse_expression()?;
            let arg_expr = self.parse_with_no_paren_calls(arg_expr)?;

            // Convert to method call: expr.to(arg) or expr.not_to(arg)
            expr = Expr::MethodCall {
                receiver: Box::new(expr),
                method: method_name.to_string(),
                args: vec![Argument {
                    name: None,
                    value: arg_expr,
                }],
            };
        }
        Ok(expr)
    }

    /// Check if an expression can be a callee for no-parens calls
    fn is_callable_expr(&self, expr: &Expr) -> bool {
        matches!(
            expr,
            Expr::Identifier(_) | Expr::FieldAccess { .. } | Expr::Path(_)
        )
    }

    /// Check if we're at a colon-block pattern: `:` followed by newline and indent
    /// This is used to distinguish `func:` blocks from `func name: value` named args
    fn is_at_colon_block(&mut self) -> bool {
        if !self.check(&TokenKind::Colon) {
            return false;
        }

        // Peek ahead to see if there's a newline after the colon
        self.peek_is(&TokenKind::Newline)
    }

    /// Check if current token can start an argument (for no-parens calls)
    fn can_start_argument(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Integer(_)
                | TokenKind::TypedInteger(_, _)
                | TokenKind::Float(_)
                | TokenKind::TypedFloat(_, _)
                | TokenKind::String(_)
                | TokenKind::RawString(_)
                | TokenKind::TypedString(_, _)
                | TokenKind::TypedRawString(_, _)
                | TokenKind::FString(_)
                | TokenKind::Bool(_)
                | TokenKind::Nil
                | TokenKind::Symbol(_)
                | TokenKind::Identifier { .. }
                | TokenKind::Result
                | TokenKind::Type
                | TokenKind::Out
                | TokenKind::OutErr
                | TokenKind::Context
                | TokenKind::Feature
                | TokenKind::Scenario
                | TokenKind::Given
                | TokenKind::When
                | TokenKind::Then
                | TokenKind::Common
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
                | TokenKind::Backslash
                | TokenKind::Colon
                | TokenKind::Await
                | TokenKind::Yield
                | TokenKind::Not
                | TokenKind::Minus
                | TokenKind::Plus
                | TokenKind::Tilde
                | TokenKind::Ampersand
                | TokenKind::Star
        )
    }

    /// Parse arguments without parentheses.
    /// - Normal mode: comma-separated (required)
    /// - Strict mode: commas optional, space-separated allowed
    fn parse_no_paren_arguments(&mut self) -> Result<Vec<Argument>, ParseError> {
        let mut args = Vec::new();

        // Parse first argument
        if let Ok(arg) = self.parse_single_argument() {
            args.push(arg);
        } else {
            return Ok(args);
        }

        // Parse remaining arguments
        loop {
            // Check for comma (required in normal mode, optional in strict mode)
            let has_comma = self.check(&TokenKind::Comma);
            if has_comma {
                self.advance(); // consume comma
            }

            // In strict mode, continue parsing if we can start another argument
            // In normal mode, require comma to continue
            if self.mode == ParserMode::Strict {
                // Strict mode: commas optional, continue if can start argument
                if !self.can_start_argument() {
                    break;
                }
            } else {
                // Normal mode: require comma to continue
                if !has_comma {
                    break;
                }
            }

            // Parse next argument
            if let Ok(arg) = self.parse_single_argument() {
                args.push(arg);
            } else {
                break;
            }
        }

        Ok(args)
    }

    /// Parse a single argument (possibly named)
    fn parse_single_argument(&mut self) -> Result<Argument, ParseError> {
        // Check for named argument: name: value
        if let TokenKind::Identifier { name: name, .. } = &self.current.kind {
            let name_clone = name.clone();
            // Peek ahead to check for colon
            if self.peek_is(&TokenKind::Colon) {
                self.advance(); // consume identifier
                self.advance(); // consume colon
                                // In strict mode, track depth when parsing named argument value
                let prev_depth = self.no_paren_depth;
                if self.mode == ParserMode::Strict {
                    self.no_paren_depth += 1;
                }
                let value = self.parse_expression()?;
                self.no_paren_depth = prev_depth;
                return Ok(Argument {
                    name: Some(name_clone),
                    value,
                });
            }
        }
        // Positional argument
        // In strict mode, track depth when parsing argument value
        let prev_depth = self.no_paren_depth;
        if self.mode == ParserMode::Strict {
            self.no_paren_depth += 1;
        }
        let value = self.parse_expression()?;
        self.no_paren_depth = prev_depth;
        Ok(Argument { name: None, value })
    }
}
