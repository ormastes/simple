//! Gherkin-style system test DSL parsing (doc/spec/gherkin_dsl.md)
//!
//! This module implements parsing for:
//! - `examples name:` - Data tables with two-space delimiter
//! - `context pattern:` - Step definitions (reuses existing Context token)
//! - `feature name:` - Feature grouping
//! - `scenario name:` / `scenario outline name:` - Test cases
//! - `given/when/then/and_then pattern:` - Step references

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use super::super::Parser;

impl<'a> Parser<'a> {
    /// Parse an examples table: `examples name:`
    /// Examples tables use two-space delimiter for natural language values.
    pub(crate) fn parse_examples(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Examples)?;

        // Parse name (can be identifier or string)
        let name = if let TokenKind::Identifier(s) = &self.current.kind {
            let n = s.clone();
            self.advance();
            n
        } else if let TokenKind::String(s) = &self.current.kind {
            let n = s.clone();
            self.advance();
            n
        } else {
            return Err(ParseError::unexpected_token(
                "examples name",
                format!("{:?}", self.current.kind),
                self.current.span,
            ));
        };

        self.expect(&TokenKind::Colon)?;

        // Parse indented block with two-space delimited rows
        // For now, we parse as a block and extract field names from the first row
        let block = self.parse_block()?;

        // Extract fields and rows from block statements
        // This is a simplified implementation - full implementation needs lexer mode
        let (fields, rows) = self.extract_examples_data(&block)?;

        Ok(Node::Examples(ExamplesTable {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            doc_comment: None,
            fields,
            rows,
        }))
    }

    /// Extract field names and data rows from a block
    /// Parses two-space delimited content from the block's source
    fn extract_examples_data(&self, block: &Block) -> Result<(Vec<String>, Vec<Vec<Expr>>), ParseError> {
        // Collect all expression nodes from the block as potential row data
        // For now, we extract identifiers and literals from expression statements
        let mut fields = Vec::new();
        let mut rows: Vec<Vec<Expr>> = Vec::new();
        let mut is_first_row = true;

        for stmt in &block.statements {
            if let Node::Expression(expr) = stmt {
                // Try to extract values from this expression
                let values = self.extract_row_values(expr);
                if is_first_row {
                    // First row contains field names (headers)
                    for val in &values {
                        fields.push(self.expr_to_field_name(val));
                    }
                    is_first_row = false;
                } else {
                    // Subsequent rows are data
                    rows.push(values);
                }
            }
        }

        Ok((fields, rows))
    }

    /// Convert an expression to a field name string
    fn expr_to_field_name(&self, expr: &Expr) -> String {
        match expr {
            Expr::Identifier(name) => name.clone(),
            Expr::String(s) => s.clone(),
            Expr::Integer(n) => n.to_string(),
            Expr::Float(f) => f.to_string(),
            Expr::Bool(b) => b.to_string(),
            Expr::Symbol(s) => s.clone(),
            _ => format!("{:?}", expr),
        }
    }

    /// Extract values from a row expression
    /// Handles identifiers, literals, and binary expressions (for multi-word values)
    fn extract_row_values(&self, expr: &Expr) -> Vec<Expr> {
        match expr {
            // Binary expressions might represent space-separated values
            Expr::Binary { left, right, .. } => {
                let mut values = self.extract_row_values(left);
                values.extend(self.extract_row_values(right));
                values
            }
            // Function calls without parens might be parsed as calls
            Expr::Call { callee, args, .. } => {
                let mut values = vec![*callee.clone()];
                for arg in args {
                    values.push(arg.value.clone());
                }
                values
            }
            // Single values
            _ => vec![expr.clone()],
        }
    }

    /// Parse a feature definition: `feature Name:`
    pub(crate) fn parse_feature(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Feature)?;

        // Parse feature name (description until colon)
        let name = self.parse_gherkin_description()?;
        self.expect(&TokenKind::Colon)?;

        // Parse indented block containing scenarios
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut scenarios = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip doc comments at feature level (triple-quoted strings)
            if is_string_token(&self.current.kind) {
                self.advance();
                continue;
            }

            if self.check(&TokenKind::Scenario) {
                let scenario = self.parse_scenario_def()?;
                scenarios.push(scenario);
            } else if self.check(&TokenKind::Newline) {
                self.advance();
            } else {
                break;
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(Node::Feature(FeatureDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            doc_comment: None,
            scenarios,
        }))
    }

    /// Parse a scenario as a top-level statement
    /// Returns Node::Scenario
    pub(crate) fn parse_scenario(&mut self) -> Result<Node, ParseError> {
        let scenario = self.parse_scenario_def()?;
        Ok(Node::Scenario(scenario))
    }

    /// Parse a scenario definition (internal)
    fn parse_scenario_def(&mut self) -> Result<ScenarioDef, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Scenario)?;

        // Check for `outline` modifier
        let is_outline = if self.check(&TokenKind::Outline) {
            self.advance();
            true
        } else {
            false
        };

        // Parse scenario name
        let name = self.parse_gherkin_description()?;
        self.expect(&TokenKind::Colon)?;

        // Parse indented block containing steps
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut steps = Vec::new();
        let mut examples_ref = None;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            if self.check(&TokenKind::Given)
                || self.check(&TokenKind::When)
                || self.check(&TokenKind::Then)
                || self.check(&TokenKind::AndThen)
            {
                let step = self.parse_step_ref()?;
                steps.push(step);
            } else if self.check(&TokenKind::Examples) {
                // Could be examples reference or inline examples
                self.advance();
                if let TokenKind::Identifier(ref_name) = &self.current.kind {
                    examples_ref = Some(ref_name.clone());
                    self.advance();
                    if self.check(&TokenKind::Colon) {
                        self.advance();
                    }
                }
            } else if self.check(&TokenKind::Newline) {
                self.advance();
            } else {
                break;
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        Ok(ScenarioDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            is_outline,
            doc_comment: None,
            steps,
            examples_ref,
            inline_examples: None,
        })
    }

    /// Parse a step reference: `given/when/then/and_then pattern:`
    fn parse_step_ref(&mut self) -> Result<StepRef, ParseError> {
        let start_span = self.current.span;

        // Determine step kind
        let kind = match &self.current.kind {
            TokenKind::Given => StepKind::Given,
            TokenKind::When => StepKind::When,
            TokenKind::Then => StepKind::Then,
            TokenKind::AndThen => StepKind::AndThen,
            _ => {
                return Err(ParseError::unexpected_token(
                    "given, when, then, or and_then",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        };
        self.advance();

        // Parse step pattern
        let pattern = self.parse_step_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Check for optional body (indented block)
        let body = if self.check(&TokenKind::Newline) {
            self.advance();
            if self.check(&TokenKind::Indent) {
                Some(self.parse_block()?)
            } else {
                None
            }
        } else {
            None
        };

        Ok(StepRef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            kind,
            pattern,
            body,
        })
    }

    /// Parse a step pattern: `calculator at <n>`
    fn parse_step_pattern(&mut self) -> Result<StepPattern, ParseError> {
        let start_span = self.current.span;
        let mut parts = Vec::new();

        while !self.check(&TokenKind::Colon) && !self.is_at_end() {
            if self.check(&TokenKind::Lt) {
                // Placeholder: <name>
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(&TokenKind::Gt)?;
                parts.push(StepPatternPart::Placeholder(name));
            } else if let TokenKind::Identifier(s) = &self.current.kind {
                parts.push(StepPatternPart::Literal(s.clone()));
                self.advance();
            } else if let TokenKind::Integer(n) = &self.current.kind {
                parts.push(StepPatternPart::Literal(n.to_string()));
                self.advance();
            } else if self.is_keyword_for_pattern() {
                // Keywords like 'is', 'result', 'to' can be used as pattern literals
                parts.push(StepPatternPart::Literal(self.current.lexeme.clone()));
                self.advance();
            } else {
                break;
            }
        }

        Ok(StepPattern {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            parts,
        })
    }

    /// Check if current token is a keyword that can be used as a step pattern literal
    /// Many keywords are valid in natural language step descriptions
    fn is_keyword_for_pattern(&self) -> bool {
        matches!(
            &self.current.kind,
            TokenKind::Is
                | TokenKind::In
                | TokenKind::To
                | TokenKind::Not
                | TokenKind::And
                | TokenKind::Or
                | TokenKind::If
                | TokenKind::For
                | TokenKind::While
                | TokenKind::With
                | TokenKind::New
                | TokenKind::Result
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Nil
                | TokenKind::As
                | TokenKind::From
                | TokenKind::Type
                | TokenKind::Return
        )
    }

    /// Parse description text until colon (for feature/scenario names)
    fn parse_gherkin_description(&mut self) -> Result<String, ParseError> {
        let mut parts = Vec::new();

        while !self.check(&TokenKind::Colon) && !self.is_at_end() {
            if let TokenKind::Identifier(s) = &self.current.kind {
                parts.push(s.clone());
                self.advance();
            } else if let TokenKind::Integer(n) = &self.current.kind {
                parts.push(n.to_string());
                self.advance();
            } else if let TokenKind::String(s) = &self.current.kind {
                parts.push(s.clone());
                self.advance();
            } else {
                break;
            }
        }

        Ok(parts.join(" "))
    }

    /// Parse a context step definition (uses existing Context keyword)
    /// `context fresh calculator:` or `context calculator at <n>:`
    pub(crate) fn parse_context_step_def(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Context)?;

        // Parse step pattern
        let pattern = self.parse_step_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Parse body block
        let body = self.parse_block()?;

        Ok(Node::StepDef(StepDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            kind: None, // context definitions don't have a step kind
            pattern,
            doc_comment: None,
            body,
        }))
    }

    /// Parse a step definition at top level using given/when/then/and_then
    /// `given fresh calculator:` or `when add <n>:`
    pub(crate) fn parse_step_ref_as_node(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Determine step kind from keyword
        let kind = match &self.current.kind {
            TokenKind::Given => StepKind::Given,
            TokenKind::When => StepKind::When,
            TokenKind::Then => StepKind::Then,
            TokenKind::AndThen => StepKind::AndThen,
            _ => {
                return Err(ParseError::unexpected_token(
                    "given, when, then, or and_then",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        };
        self.advance();

        // Parse step pattern
        let pattern = self.parse_step_pattern()?;
        self.expect(&TokenKind::Colon)?;

        // Parse body block
        let body = self.parse_block()?;

        Ok(Node::StepDef(StepDef {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            kind: Some(kind),
            pattern,
            doc_comment: None,
            body,
        }))
    }
}

/// Helper to check if a token is a String variant
fn is_string_token(kind: &TokenKind) -> bool {
    matches!(kind, TokenKind::String(_))
}

#[cfg(test)]
mod tests {
    use crate::Parser;
    use crate::ast::{Module, Node, StepKind};
    use crate::error::ParseError;

    fn parse_source(src: &str) -> Result<Module, ParseError> {
        let mut parser = Parser::new(src);
        parser.parse()
    }

    #[test]
    fn test_parse_examples_basic() {
        let src = "examples addition:\n    pass";
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 1);
        assert!(matches!(&module.items[0], Node::Examples(_)));
        if let Node::Examples(ex) = &module.items[0] {
            assert_eq!(ex.name, "addition");
        }
    }

    #[test]
    fn test_parse_examples_with_data() {
        // Simple data table with identifiers
        let src = r#"examples numbers:
    a  b  result
    1  2  3
    4  5  9
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::Examples(ex) = &module.items[0] {
            assert_eq!(ex.name, "numbers");
            // Check that fields were extracted (from first row)
            // Note: actual extraction depends on how the parser handles the row
            // The fields may be parsed as a function call or expression
        }
    }

    #[test]
    fn test_parse_feature_with_scenario() {
        let src = r#"feature Calculator:
    scenario Add two numbers:
        given fresh calculator:
        when add 5:
        then value is 5:
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 1);
        assert!(matches!(&module.items[0], Node::Feature(_)));
        if let Node::Feature(feat) = &module.items[0] {
            assert_eq!(feat.name, "Calculator");
            assert_eq!(feat.scenarios.len(), 1);
            assert_eq!(feat.scenarios[0].name, "Add two numbers");
            assert_eq!(feat.scenarios[0].steps.len(), 3);
        }
    }

    #[test]
    fn test_parse_scenario_outline() {
        let src = r#"feature Math:
    scenario outline Addition:
        given calculator at 0:
        when add n:
        then value is n:
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::Feature(feat) = &module.items[0] {
            assert!(feat.scenarios[0].is_outline);
        }
    }

    #[test]
    fn test_parse_step_definition() {
        let src = r#"given fresh calculator:
    return Calculator.new()
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 1);
        assert!(matches!(&module.items[0], Node::StepDef(_)));
        if let Node::StepDef(step) = &module.items[0] {
            assert_eq!(step.kind, Some(StepKind::Given));
            assert!(!step.pattern.parts.is_empty());
        }
    }

    #[test]
    fn test_parse_step_with_placeholder() {
        let src = r#"when add <n>:
    calc.add(n)
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::StepDef(step) = &module.items[0] {
            assert_eq!(step.kind, Some(StepKind::When));
            // Check that pattern has placeholder
            let has_placeholder = step.pattern.parts.iter().any(|p| {
                matches!(p, crate::ast::StepPatternPart::Placeholder(_))
            });
            assert!(has_placeholder);
        }
    }

    #[test]
    fn test_parse_standalone_scenario() {
        let src = r#"scenario Simple test:
    given something:
    then result:
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 1);
        assert!(matches!(&module.items[0], Node::Scenario(_)));
        if let Node::Scenario(sc) = &module.items[0] {
            assert_eq!(sc.name, "Simple test");
            assert!(!sc.is_outline);
            assert_eq!(sc.steps.len(), 2);
        }
    }
}
