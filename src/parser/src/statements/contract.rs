/// Contract block parsing for LLM-friendly feature #400
///
/// This module handles parsing of:
/// - requires: blocks (preconditions)
/// - ensures: blocks (postconditions)
/// - invariant: blocks (class invariants)
/// - old(expr) expressions
/// - result identifiers
use crate::ast::{ContractBlock, ContractClause, Expr, InvariantBlock};
use crate::error::ParseError;
use crate::parser::Parser;
use crate::token::{Span, TokenKind};

impl Parser<'_> {
    /// Parse a contract block (requires/ensures) for a function.
    ///
    /// Syntax:
    /// ```text
    /// requires:
    ///     condition1
    ///     condition2
    /// ensures:
    ///     res > 0
    ///     res * b == a
    /// ```
    pub(crate) fn parse_contract_block(&mut self) -> Result<Option<ContractBlock>, ParseError> {
        let mut requires = Vec::new();
        let mut ensures = Vec::new();

        // Check for requires block
        if self.check(&TokenKind::Requires) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            // Parse all requires clauses
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                let clause = self.parse_contract_clause()?;
                requires.push(clause);
                self.skip_newlines();
            }

            self.expect(&TokenKind::Dedent)?;
        }

        // Check for ensures block
        if self.check(&TokenKind::Ensures) {
            self.advance();
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            // Parse all ensures clauses
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                let clause = self.parse_contract_clause()?;
                ensures.push(clause);
                self.skip_newlines();
            }

            self.expect(&TokenKind::Dedent)?;
        }

        // Return None if no contract blocks found
        if requires.is_empty() && ensures.is_empty() {
            Ok(None)
        } else {
            Ok(Some(ContractBlock { requires, ensures }))
        }
    }

    /// Parse a single contract clause (one condition).
    ///
    /// Syntax:
    /// ```text
    /// b != 0
    /// res > 0
    /// balance >= 0
    /// ```
    fn parse_contract_clause(&mut self) -> Result<ContractClause, ParseError> {
        let start_span = self.current.span;
        let condition = self.parse_expression()?;

        // TODO: Optional error message: condition, "message"
        let message = None;

        Ok(ContractClause {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            condition,
            message,
        })
    }

    /// Parse an invariant block for a class.
    ///
    /// Syntax:
    /// ```text
    /// invariant:
    ///     balance >= 0
    ///     count >= 0
    /// ```
    pub(crate) fn parse_invariant_block(&mut self) -> Result<Option<InvariantBlock>, ParseError> {
        if !self.check(&TokenKind::Invariant) {
            return Ok(None);
        }

        let start_span = self.current.span;
        self.advance();
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut conditions = Vec::new();

        // Parse all invariant conditions
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            let clause = self.parse_contract_clause()?;
            conditions.push(clause);
            self.skip_newlines();
        }

        self.expect(&TokenKind::Dedent)?;

        Ok(Some(InvariantBlock {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            conditions,
        }))
    }

    /// Handle old() and result in contract expressions.
    ///
    /// This is called from expression parsing when we encounter
    /// the 'old' identifier or 'result' identifier in a contract context.
    pub(crate) fn parse_contract_special_expr(&mut self) -> Result<Expr, ParseError> {
        let token = self.current.clone();

        match &token.kind {
            TokenKind::Old => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let expr = self.parse_expression()?;
                self.expect(&TokenKind::RParen)?;
                Ok(Expr::ContractOld(Box::new(expr)))
            }
            TokenKind::Identifier(name) if name == "result" => {
                self.advance();
                Ok(Expr::ContractResult)
            }
            _ => {
                // Not a contract special expression, parse as normal
                self.parse_primary()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_requires_block() {
        let source = r#"
requires:
    b != 0
    a > 0
"#;
        let mut parser = Parser::new(source);
        // TODO: Add test when contract parsing is wired up
    }

    #[test]
    fn test_parse_ensures_block() {
        let source = r#"
ensures:
    result > 0
    result * b == a
"#;
        let mut parser = Parser::new(source);
        // TODO: Add test when contract parsing is wired up
    }

    #[test]
    fn test_parse_invariant_block() {
        let source = r#"
invariant:
    balance >= 0
    count >= 0
"#;
        let mut parser = Parser::new(source);
        // TODO: Add test when contract parsing is wired up
    }
}
