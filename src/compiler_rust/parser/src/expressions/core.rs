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
        let result = self.parse_pipe();
        // Consume matching DEDENTs for any INDENTs consumed during binary operator
        // line continuation.
        let consumed = self.binary_indent_count;
        self.binary_indent_count = saved_indent_count;
        if consumed > 0 {
            self.consume_dedents_for_method_chain(consumed);
        }
        result
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
