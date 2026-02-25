/// Contract block parsing for LLM-friendly feature #400
///
/// This module handles parsing of contract specifications per doc/spec/invariant.md:
///
/// New spec syntax:
/// - in: blocks (preconditions)
/// - invariant: blocks (routine invariants)
/// - out(ret): blocks (postconditions for success)
/// - out_err(err): blocks (postconditions for error)
/// - old(expr) expressions
///
/// Legacy syntax (still supported):
/// - requires: blocks (preconditions)
/// - ensures: blocks (postconditions)
/// - result identifiers
use crate::ast::{ContractBlock, ContractClause, InvariantBlock};
use crate::error::ParseError;
use crate::parser::Parser;
use crate::token::{Span, TokenKind};

impl Parser<'_> {
    /// Parse entry contract blocks (in:, invariant:, requires:) at the start of function body.
    ///
    /// New spec syntax:
    /// ```text
    /// in:
    ///     b != 0
    ///     a > 0
    /// invariant:
    ///     balance >= 0
    /// ```
    ///
    /// Legacy syntax:
    /// ```text
    /// requires:
    ///     b != 0
    /// ```
    pub(crate) fn parse_entry_contracts(&mut self) -> Result<ContractBlock, ParseError> {
        let mut contract = ContractBlock::default();

        // Parse in: block (new spec) or requires: block (legacy)
        if self.check(&TokenKind::In) || self.check(&TokenKind::Requires) {
            self.advance();
            self.parse_contract_clause_block(&mut contract.preconditions)?;
        }

        // Parse routine invariant: block (at function entry)
        if self.check(&TokenKind::Invariant) {
            self.advance();
            self.parse_contract_clause_block(&mut contract.invariants)?;
        }

        Ok(contract)
    }

    /// Helper to parse an indented contract clause block
    fn parse_contract_clause_block(&mut self, clauses: &mut Vec<ContractClause>) -> Result<(), ParseError> {
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        if !self.check(&TokenKind::Indent) {
            // Empty contract block
            return Ok(());
        }
        self.expect(&TokenKind::Indent)?;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            let clause = self.parse_contract_clause()?;
            clauses.push(clause);
            self.skip_newlines();
        }
        self.expect(&TokenKind::Dedent)?;
        Ok(())
    }

    /// Parse exit contract blocks (out(ret):, out_err(err):, ensures:) at end of function body.
    ///
    /// New spec syntax:
    /// ```text
    /// out(ret):
    ///     ret > 0
    ///     ret * b == a
    /// out_err(err):
    ///     err.msg != ""
    /// ```
    ///
    /// Legacy syntax:
    /// ```text
    /// ensures:
    ///     result > 0
    /// ```
    pub(crate) fn parse_exit_contracts(&mut self, contract: &mut ContractBlock) -> Result<(), ParseError> {
        // Parse out(ret): block (new spec)
        if self.check(&TokenKind::Out) {
            self.advance();
            self.expect(&TokenKind::LParen)?;

            // Parse the binding name (default: ret)
            let binding = if let TokenKind::Identifier(name) = &self.current.kind {
                let name = name.clone();
                self.advance();
                name
            } else {
                "ret".to_string()
            };
            contract.postcondition_binding = Some(binding);

            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            if !self.check(&TokenKind::Indent) {
                // Empty out(ret): block — skip
            } else {
                self.expect(&TokenKind::Indent)?;

                while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                    let clause = self.parse_contract_clause()?;
                    contract.postconditions.push(clause);
                    self.skip_newlines();
                }
                self.expect(&TokenKind::Dedent)?;
            }
        } else if self.check(&TokenKind::Ensures) {
            // Legacy ensures: block
            self.advance();
            self.parse_contract_clause_block(&mut contract.postconditions)?;
        }

        // Parse out_err(err): block (new spec)
        if self.check(&TokenKind::OutErr) {
            self.advance();
            self.expect(&TokenKind::LParen)?;

            // Parse the binding name (default: err)
            let binding = if let TokenKind::Identifier(name) = &self.current.kind {
                let name = name.clone();
                self.advance();
                name
            } else {
                "err".to_string()
            };
            contract.error_binding = Some(binding);

            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            if !self.check(&TokenKind::Indent) {
                // Empty out_err(err): block — skip
            } else {
                self.expect(&TokenKind::Indent)?;

                while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                    let clause = self.parse_contract_clause()?;
                    contract.error_postconditions.push(clause);
                    self.skip_newlines();
                }
                self.expect(&TokenKind::Dedent)?;
            }
        }

        Ok(())
    }

    /// Parse a contract block (combines entry and exit contracts).
    ///
    /// Supports both new spec syntax (in:/out(ret):/out_err(err):/invariant:)
    /// and legacy syntax (requires:/ensures:).
    pub(crate) fn parse_contract_block(&mut self) -> Result<Option<ContractBlock>, ParseError> {
        let mut contract = self.parse_entry_contracts()?;

        // Parse exit contracts (new spec syntax)
        self.parse_exit_contracts(&mut contract)?;

        if contract.is_empty() {
            Ok(None)
        } else {
            Ok(Some(contract))
        }
    }

    /// Parse a single contract clause (one condition).
    ///
    /// Syntax:
    /// ```text
    /// b != 0
    /// ret > 0
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

    /// Parse a type/class invariant block.
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
        if !self.check(&TokenKind::Indent) {
            // Empty invariant block
            return Ok(Some(InvariantBlock {
                span: Span::new(start_span.start, self.previous.span.end, start_span.line, start_span.column),
                conditions: vec![],
            }));
        }
        self.expect(&TokenKind::Indent)?;

        let mut conditions = Vec::new();

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

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_in_block() {
        let source = r#"
in:
    b != 0
    a > 0
"#;
        let mut parser = Parser::new(source);
        parser.skip_newlines(); // skip initial newlines
        let contract = parser.parse_entry_contracts().unwrap();
        assert_eq!(contract.preconditions.len(), 2);
    }

    #[test]
    fn test_parse_requires_block() {
        let source = r#"
requires:
    b != 0
    a > 0
"#;
        let mut parser = Parser::new(source);
        parser.skip_newlines();
        let contract = parser.parse_entry_contracts().unwrap();
        assert_eq!(contract.preconditions.len(), 2);
    }

    #[test]
    fn test_parse_invariant_in_function() {
        let source = r#"
invariant:
    balance >= 0
"#;
        let mut parser = Parser::new(source);
        parser.skip_newlines();
        let contract = parser.parse_entry_contracts().unwrap();
        assert_eq!(contract.invariants.len(), 1);
    }

    /// Helper to parse a contract block from source
    fn parse_contract(source: &str) -> Option<ContractBlock> {
        let mut parser = Parser::new(source);
        parser.skip_newlines();
        parser.parse_contract_block().unwrap()
    }

    #[test]
    fn test_parse_class_invariant() {
        let source = r#"
invariant:
    balance >= 0
    count >= 0
"#;
        let mut parser = Parser::new(source);
        parser.skip_newlines();
        let inv = parser.parse_invariant_block().unwrap();
        assert!(inv.is_some());
        assert_eq!(inv.unwrap().conditions.len(), 2);
    }

    #[test]
    fn test_parse_out_block() {
        let source = r#"
out(ret):
    ret > 0
    ret * b == a
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.postconditions.len(), 2);
        assert_eq!(contract.postcondition_binding, Some("ret".to_string()));
    }

    #[test]
    fn test_parse_out_err_block() {
        let source = r#"
out_err(e):
    e != nil
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.error_postconditions.len(), 1);
        assert_eq!(contract.error_binding, Some("e".to_string()));
    }

    #[test]
    fn test_parse_combined_contracts() {
        let source = r#"
in:
    a > 0
    b != 0
out(ret):
    ret >= 0
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.preconditions.len(), 2);
        assert_eq!(contract.postconditions.len(), 1);
    }
}
