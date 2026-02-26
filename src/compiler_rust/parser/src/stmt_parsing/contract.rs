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
use crate::ast::{ContractBlock, ContractClause, Expr, InvariantBlock};
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl Parser<'_> {
    /// Parse entry contract blocks (in:, invariant:, requires:, decreases:) at the start of function body.
    ///
    /// New spec syntax:
    /// ```text
    /// in:
    ///     b != 0
    ///     a > 0
    /// invariant:
    ///     balance >= 0
    /// decreases:
    ///     n
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

        // Parse decreases: block (termination measure for Lean verification)
        // This is not checked at runtime, only used for Lean termination_by
        if self.check(&TokenKind::Decreases) {
            self.advance();
            contract.decreases = Some(self.parse_decreases_clause()?);
        }

        // Parse proof uses: theorem_name (VER-022: Proof Import/Reuse)
        // References an existing Lean theorem from lean{} blocks
        if let TokenKind::Identifier { name, .. } = &self.current.kind {
            if name == "proof" {
                // Peek ahead to check if next token is "uses"
                let next = self.peek_next();
                if matches!(&next.kind, TokenKind::Identifier { name, .. } if name == "uses") {
                    self.advance(); // consume "proof"
                    self.advance(); // consume "uses"
                    self.expect(&TokenKind::Colon)?;

                    // Parse the theorem name
                    if let TokenKind::Identifier { name, .. } = &self.current.kind {
                        contract.proof_uses = Some(name.clone());
                        self.advance();
                        self.skip_newlines();
                    } else {
                        return Err(ParseError::syntax_error_with_span(
                            "expected theorem name after 'proof uses:'",
                            self.current.span,
                        ));
                    }
                }
            }
        }

        Ok(contract)
    }

    /// Parse a single decreases clause (termination measure).
    ///
    /// Syntax:
    /// ```text
    /// decreases:
    ///     n
    /// ```
    /// or inline:
    /// ```text
    /// decreases: n
    /// ```
    fn parse_decreases_clause(&mut self) -> Result<ContractClause, ParseError> {
        self.debug_enter("parse_decreases_clause");
        self.expect(&TokenKind::Colon)?;

        // Check if it's inline (same line) or block (indented)
        if self.check(&TokenKind::Newline) {
            // Block style: decreases:\n    expr
            self.advance();
            self.expect(&TokenKind::Indent)?;
            let clause = self.parse_contract_clause()?;
            self.skip_newlines();
            self.expect(&TokenKind::Dedent)?;
            self.debug_exit("parse_decreases_clause");
            Ok(clause)
        } else {
            // Inline style: decreases: expr
            let clause = self.parse_contract_clause()?;
            self.skip_newlines();
            self.debug_exit("parse_decreases_clause");
            Ok(clause)
        }
    }

    /// Helper to parse an indented contract clause block
    fn parse_contract_clause_block(&mut self, clauses: &mut Vec<ContractClause>) -> Result<(), ParseError> {
        self.debug_enter("parse_contract_clause_block");
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut iterations = 0usize;
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "contract_clause_block")?;
            iterations += 1;

            let clause = self.parse_contract_clause()?;
            clauses.push(clause);
            self.skip_newlines();
        }
        self.expect(&TokenKind::Dedent)?;
        self.debug_exit("parse_contract_clause_block");
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
            // Allow underscore to skip binding (out(_):)
            let binding = if self.check(&TokenKind::Underscore) {
                self.advance();
                None
            } else if let TokenKind::Identifier { name, .. } = &self.current.kind {
                let name = name.clone();
                self.advance();
                Some(name)
            } else {
                Some("ret".to_string())
            };
            contract.postcondition_binding = binding;

            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            let mut iterations = 0usize;
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                self.check_loop_limit(iterations, "exit_contracts:out")?;
                iterations += 1;

                let clause = self.parse_contract_clause()?;
                contract.postconditions.push(clause);
                self.skip_newlines();
            }
            self.expect(&TokenKind::Dedent)?;
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
            // Allow underscore to skip binding (out_err(_):)
            let binding = if self.check(&TokenKind::Underscore) {
                self.advance();
                None
            } else if let TokenKind::Identifier { name, .. } = &self.current.kind {
                let name = name.clone();
                self.advance();
                Some(name)
            } else {
                Some("err".to_string())
            };
            contract.error_binding = binding;

            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Colon)?;
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            let mut iterations = 0usize;
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                self.check_loop_limit(iterations, "exit_contracts:out_err")?;
                iterations += 1;

                let clause = self.parse_contract_clause()?;
                contract.error_postconditions.push(clause);
                self.skip_newlines();
            }
            self.expect(&TokenKind::Dedent)?;
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

        // Optional error message support: condition, "message"
        // Currently not implemented - all contracts use default error messages
        // Future: Check for comma, parse string literal for custom message
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

        self.debug_enter("parse_invariant_block");
        let start_span = self.current.span;
        self.advance();
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut conditions = Vec::new();
        let mut iterations = 0usize;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "invariant_block")?;
            iterations += 1;

            let clause = self.parse_contract_clause()?;
            conditions.push(clause);
            self.skip_newlines();
        }

        self.expect(&TokenKind::Dedent)?;
        self.debug_exit("parse_invariant_block");

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

    /// Handle old() and result/ret/err in contract expressions.
    ///
    /// This is called from expression parsing when we encounter
    /// the 'old' identifier or contract binding identifiers.
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
            // Legacy: result identifier
            TokenKind::Result => {
                self.advance();
                Ok(Expr::ContractResult)
            }
            TokenKind::Identifier { name, .. } if name == "result" => {
                self.advance();
                Ok(Expr::ContractResult)
            }
            _ => {
                // Not a contract special expression, parse as normal
                self.parse_primary()
            }
        }
    }

    /// Check if current position looks like an exit contract block.
    pub(crate) fn is_exit_contract(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Out | TokenKind::OutErr | TokenKind::Ensures
        )
    }

    /// Parse loop invariant clauses at the start of a loop body.
    ///
    /// Syntax:
    /// ```text
    /// for i in 0..n:
    ///     invariant: sum == partial_sum(i)
    ///     sum = sum + arr[i]
    ///
    /// while x > 0:
    ///     invariant: x * y == original
    ///     x = x - 1
    /// ```
    ///
    /// Returns the invariant clauses (may be empty if no invariants present).
    pub(crate) fn parse_loop_invariants(&mut self) -> Result<Vec<ContractClause>, ParseError> {
        let mut invariants = Vec::new();

        // Check for invariant: keyword
        while self.check(&TokenKind::Invariant) {
            self.advance();
            self.expect(&TokenKind::Colon)?;

            // Parse the invariant expression(s)
            // Can be inline (same line) or block (indented)
            if self.check(&TokenKind::Newline) {
                // Block style: invariant:\n    expr\n    expr
                self.advance();
                self.expect(&TokenKind::Indent)?;

                let mut iterations = 0usize;
                while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                    self.check_loop_limit(iterations, "loop_invariant_block")?;
                    iterations += 1;

                    let clause = self.parse_contract_clause()?;
                    invariants.push(clause);
                    self.skip_newlines();
                }
                self.expect(&TokenKind::Dedent)?;
            } else {
                // Inline style: invariant: expr
                let clause = self.parse_contract_clause()?;
                invariants.push(clause);
                self.skip_newlines();
            }
        }

        Ok(invariants)
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

    #[test]
    fn test_parse_decreases_block() {
        let source = r#"
requires:
    n >= 0
decreases:
    n
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.preconditions.len(), 1);
        assert!(contract.decreases.is_some());
        assert!(contract.has_decreases());
    }

    #[test]
    fn test_parse_decreases_inline() {
        let source = r#"
requires:
    n >= 0
decreases: n
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.preconditions.len(), 1);
        assert!(contract.decreases.is_some());
    }

    #[test]
    fn test_parse_full_verification_contract() {
        let source = r#"
in:
    n >= 0
decreases:
    n
out(ret):
    ret >= 1
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.preconditions.len(), 1);
        assert!(contract.decreases.is_some());
        assert_eq!(contract.postconditions.len(), 1);
    }

    #[test]
    fn test_parse_out_underscore() {
        let source = r#"
out(_):
    true
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.postconditions.len(), 1);
        assert_eq!(contract.postcondition_binding, None);
    }

    #[test]
    fn test_parse_out_err_underscore() {
        let source = r#"
out_err(_):
    true
"#;
        let contract = parse_contract(source).unwrap();
        assert_eq!(contract.error_postconditions.len(), 1);
        assert_eq!(contract.error_binding, None);
    }
}
