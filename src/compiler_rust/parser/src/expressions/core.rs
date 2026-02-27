use crate::ast::{Argument, Expr};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::TokenKind;

impl<'a> Parser<'a> {
    /// Helper to convert an expression + args into a Call or MethodCall.
    /// If expr is FieldAccess, create MethodCall; otherwise create Call.
    pub(super) fn make_call_expr(&self, expr: Expr, args: Vec<Argument>) -> Expr {
        match expr {
            Expr::FieldAccess { receiver, field } => Expr::MethodCall {
                receiver,
                method: field,
                args,
            },
            _ => Expr::Call {
                callee: Box::new(expr),
                args,
            },
        }
    }

    /// Helper to create a Slice expression
    pub(super) fn make_slice_expr(
        &self,
        receiver: Expr,
        start: Option<Expr>,
        end: Option<Expr>,
        step: Option<Box<Expr>>,
    ) -> Expr {
        Expr::Slice {
            receiver: Box::new(receiver),
            start: start.map(Box::new),
            end: end.map(Box::new),
            step,
        }
    }

    // === Expression Parsing (Pratt Parser) ===

    pub(crate) fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        let saved_indent_count = self.binary_indent_count;
        self.binary_indent_count = 0;
        let mut result = self.parse_pipe()?;

        // Handle postfix ternary: `expr if cond else expr`
        // Python-style conditional: `value_if_true if condition else value_if_false`
        // Only when `if` directly follows the expression (not after Dedent/Newline/Indent,
        // which would indicate a new statement on a separate line).
        if self.check(&TokenKind::If)
            && !matches!(
                self.previous.kind,
                TokenKind::Dedent | TokenKind::Newline | TokenKind::Indent
            )
        {
            self.advance(); // consume 'if'
            let condition = self.parse_pipe()?;
            self.expect(&TokenKind::Else)?;
            // Optional colon after else (Simple style: `else:`)
            if self.check(&TokenKind::Colon) {
                self.advance();
            }
            let else_expr = self.parse_pipe()?;
            result = Expr::If {
                let_pattern: None,
                condition: Box::new(condition),
                then_branch: Box::new(result),
                else_branch: Some(Box::new(else_expr)),
            };
        }

        // Consume matching DEDENTs for any INDENTs consumed during binary operator
        // line continuation.
        let consumed = self.binary_indent_count;
        self.binary_indent_count = saved_indent_count;
        if consumed > 0 {
            self.consume_dedents_for_method_chain(consumed);
        }
        Ok(result)
    }

    /// Parse optional step expression for slice syntax (`:step` at end of slice)
    pub(super) fn parse_optional_step(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::Colon) {
            self.advance();
            if self.check(&TokenKind::RBracket) {
                Ok(None)
            } else {
                Ok(Some(Box::new(self.parse_expression()?)))
            }
        } else {
            Ok(None)
        }
    }

    /// Parse optional expression before RBracket
    pub(super) fn parse_optional_expr_before_bracket(&mut self) -> Result<Option<Box<Expr>>, ParseError> {
        if self.check(&TokenKind::RBracket) {
            Ok(None)
        } else {
            Ok(Some(Box::new(self.parse_expression()?)))
        }
    }
}
