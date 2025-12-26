//! Gherkin-style system test DSL parsing (doc/spec/gherkin_dsl.md)
//!
//! This module transforms Gherkin syntax into Simple AST:
//! - `feature name:` → `feature("name", do_block)`
//! - `scenario name:` → `scenario("name", do_block)`
//! - `given/when/then/and_then pattern:` → `given("pattern", do_block)`
//! - `examples name:` → `examples("name", [rows...])`
//!
//! This allows Gherkin constructs to use existing HIR/MIR/codegen infrastructure.

use crate::ast::*;
use crate::error::ParseError;
use crate::token::{Span, TokenKind};

use crate::parser_impl::core::Parser;

impl<'a> Parser<'a> {
    /// Parse an examples table: `examples name:`
    /// Transforms to: `examples("name", [[row1...], [row2...], ...])`
    pub(crate) fn parse_examples(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Examples)?;

        // Parse name (can be identifier or string)
        let name = self.parse_gherkin_name()?;
        self.expect(&TokenKind::Colon)?;

        // Parse indented block
        let block = self.parse_block()?;

        // Extract rows as array of arrays
        let rows_expr = self.block_to_array_expr(&block, start_span);

        // Generate: examples("name", [[...], [...]])
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("examples".to_string())),
            args: vec![
                Argument { name: None, value: Expr::String(name) },
                Argument { name: None, value: rows_expr },
            ],
        };

        Ok(Node::Expression(call_expr))
    }

    /// Parse a feature definition: `feature Name:`
    /// Transforms to: `feature("Name", do_block)`
    pub(crate) fn parse_feature(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Feature)?;

        let name = self.parse_gherkin_description()?;
        self.expect(&TokenKind::Colon)?;

        // Parse body as block
        let block = self.parse_block()?;

        // Generate: feature("Name", do_block)
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier("feature".to_string())),
            args: vec![
                Argument { name: None, value: Expr::String(name) },
                Argument { name: None, value: Expr::DoBlock(block.statements) },
            ],
        };

        Ok(Node::Expression(call_expr))
    }

    /// Parse a scenario: `scenario Name:` or `scenario outline Name:`
    /// Transforms to: `scenario("Name", do_block)` or `scenario_outline("Name", do_block)`
    pub(crate) fn parse_scenario(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Scenario)?;

        // Check for `outline` modifier
        let fn_name = if self.check(&TokenKind::Outline) {
            self.advance();
            "scenario_outline"
        } else {
            "scenario"
        };

        let name = self.parse_gherkin_description()?;
        self.expect(&TokenKind::Colon)?;

        // Parse body
        let block = self.parse_block()?;

        // Generate: scenario("Name", do_block)
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier(fn_name.to_string())),
            args: vec![
                Argument { name: None, value: Expr::String(name) },
                Argument { name: None, value: Expr::DoBlock(block.statements) },
            ],
        };

        Ok(Node::Expression(call_expr))
    }

    /// Parse step keywords at top level: `given/when/then/and_then pattern:`
    /// Transforms to: `given("pattern", do_block)`
    pub(crate) fn parse_step_ref_as_node(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Determine function name from keyword
        let fn_name = match &self.current.kind {
            TokenKind::Given => "given",
            TokenKind::When => "when",
            TokenKind::Then => "then",
            TokenKind::AndThen => "and_then",
            _ => {
                return Err(ParseError::unexpected_token(
                    "given, when, then, or and_then",
                    format!("{:?}", self.current.kind),
                    self.current.span,
                ))
            }
        };
        self.advance();

        // Parse step pattern as string
        let pattern = self.parse_step_pattern_as_string()?;
        self.expect(&TokenKind::Colon)?;

        // Parse optional body block
        // Need to check for Newline followed by Indent (not just Newline)
        let body_expr = if self.check(&TokenKind::Newline) {
            // Peek ahead: is there an Indent after the Newline?
            // Save position and check
            self.advance(); // consume Newline
            if self.check(&TokenKind::Indent) {
                // There's a body block
                self.advance(); // consume Indent
                let block = self.parse_block_body()?;
                Expr::DoBlock(block.statements)
            } else {
                // No body, just a step reference
                Expr::Nil
            }
        } else {
            Expr::Nil
        };

        // Generate: given("pattern", do_block)
        let call_expr = Expr::Call {
            callee: Box::new(Expr::Identifier(fn_name.to_string())),
            args: vec![
                Argument { name: None, value: Expr::String(pattern) },
                Argument { name: None, value: body_expr },
            ],
        };

        Ok(Node::Expression(call_expr))
    }

    /// Parse a gherkin name (identifier or string)
    fn parse_gherkin_name(&mut self) -> Result<String, ParseError> {
        if let TokenKind::Identifier(s) = &self.current.kind {
            let n = s.clone();
            self.advance();
            Ok(n)
        } else if let TokenKind::String(s) = &self.current.kind {
            let n = s.clone();
            self.advance();
            Ok(n)
        } else if let TokenKind::FString(tokens) = &self.current.kind {
            // Handle f-strings (double-quoted strings)
            // For names, we only support literal f-strings (no interpolation)
            let mut s = String::new();
            for token in tokens {
                match token {
                    crate::token::FStringToken::Literal(lit) => s.push_str(lit),
                    crate::token::FStringToken::Expr(_) => {
                        return Err(ParseError::unexpected_token(
                            "plain string",
                            "string with interpolation",
                            self.current.span,
                        ));
                    }
                }
            }
            self.advance();
            Ok(s)
        } else {
            Err(ParseError::unexpected_token(
                "name",
                format!("{:?}", self.current.kind),
                self.current.span,
            ))
        }
    }

    /// Parse step pattern and return as string
    /// Handles: `fresh calculator`, `add <n>`, `value is 5`
    fn parse_step_pattern_as_string(&mut self) -> Result<String, ParseError> {
        let mut parts = Vec::new();

        while !self.check(&TokenKind::Colon) && !self.is_at_end() {
            if self.check(&TokenKind::Lt) {
                // Placeholder: <name> - keep as-is in string
                self.advance();
                let name = self.expect_identifier()?;
                self.expect(&TokenKind::Gt)?;
                parts.push(format!("<{}>", name));
            } else if let TokenKind::Identifier(s) = &self.current.kind {
                parts.push(s.clone());
                self.advance();
            } else if let TokenKind::Integer(n) = &self.current.kind {
                parts.push(n.to_string());
                self.advance();
            } else if let TokenKind::String(s) = &self.current.kind {
                parts.push(s.clone());
                self.advance();
            } else if let TokenKind::FString(tokens) = &self.current.kind {
                // Handle f-strings (double-quoted strings)
                // For step patterns, we only support literal f-strings (no interpolation)
                let mut s = String::new();
                for token in tokens {
                    match token {
                        crate::token::FStringToken::Literal(lit) => s.push_str(lit),
                        crate::token::FStringToken::Expr(_) => {
                            return Err(ParseError::unexpected_token(
                                "plain string",
                                "string with interpolation",
                                self.current.span,
                            ));
                        }
                    }
                }
                parts.push(s);
                self.advance();
            } else if self.is_keyword_for_pattern() {
                parts.push(self.current.lexeme.clone());
                self.advance();
            } else {
                break;
            }
        }

        Ok(parts.join(" "))
    }

    /// Check if current token is a keyword that can be used as a step pattern literal
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
            } else if let TokenKind::FString(tokens) = &self.current.kind {
                // Handle f-strings (double-quoted strings)
                // For gherkin descriptions, we only support literal f-strings (no interpolation)
                let mut s = String::new();
                for token in tokens {
                    match token {
                        crate::token::FStringToken::Literal(lit) => s.push_str(lit),
                        crate::token::FStringToken::Expr(_) => {
                            return Err(ParseError::unexpected_token(
                                "plain string",
                                "string with interpolation",
                                self.current.span,
                            ));
                        }
                    }
                }
                parts.push(s);
                self.advance();
            } else if self.is_keyword_for_pattern() {
                parts.push(self.current.lexeme.clone());
                self.advance();
            } else {
                break;
            }
        }

        Ok(parts.join(" "))
    }

    /// Convert a block's statements to an array expression
    /// Each statement becomes an element in the array
    fn block_to_array_expr(&self, block: &Block, span: Span) -> Expr {
        let elements: Vec<Expr> = block.statements.iter().filter_map(|stmt| {
            if let Node::Expression(expr) = stmt {
                Some(expr.clone())
            } else {
                None
            }
        }).collect();

        Expr::Array(elements)
    }
}

#[cfg(test)]
mod tests {
    use crate::parser_impl::core::Parser;
    use crate::ast::{Module, Node, Expr, Argument};
    use crate::error::ParseError;
    use crate::TokenKind;

    fn parse_source(src: &str) -> Result<Module, ParseError> {
        let mut parser = Parser::new(src);
        parser.parse()
    }

    #[test]
    fn test_parse_examples_as_call() {
        let src = "examples addition:\n    pass";
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 1);
        // Should be a function call expression
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "examples");
            }
            assert_eq!(args.len(), 2); // name and data array
        } else {
            panic!("Expected Call expression");
        }
    }

    #[test]
    fn test_parse_feature_as_call() {
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
        // Should be feature("Calculator", do_block)
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "feature");
            }
            assert_eq!(args.len(), 2);
            // First arg is name
            if let Expr::String(name) = &args[0].value {
                assert_eq!(name, "Calculator");
            }
            // Second arg is DoBlock
            assert!(matches!(&args[1].value, Expr::DoBlock(_)));
        } else {
            panic!("Expected Call expression");
        }
    }

    #[test]
    fn test_parse_scenario_as_call() {
        let src = r#"scenario Simple test:
    given something:
    then result:
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "scenario");
            }
            if let Expr::String(name) = &args[0].value {
                assert_eq!(name, "Simple test");
            }
        } else {
            panic!("Expected Call expression");
        }
    }

    #[test]
    fn test_parse_scenario_outline_as_call() {
        let src = r#"scenario outline Addition:
    given calculator at 0:
    when add n:
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::Expression(Expr::Call { callee, .. }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "scenario_outline");
            }
        } else {
            panic!("Expected Call expression");
        }
    }

    #[test]
    fn test_parse_step_as_call() {
        let src = r#"given fresh calculator:
    return Calculator.new()
"#;
        let result = parse_source(src);
        assert!(result.is_ok());
        let module = result.unwrap();
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "given");
            }
            if let Expr::String(pattern) = &args[0].value {
                assert_eq!(pattern, "fresh calculator");
            }
            // Second arg is DoBlock with body
            assert!(matches!(&args[1].value, Expr::DoBlock(_)));
        } else {
            panic!("Expected Call expression");
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
        if let Node::Expression(Expr::Call { callee, args }) = &module.items[0] {
            if let Expr::Identifier(name) = callee.as_ref() {
                assert_eq!(name, "when");
            }
            if let Expr::String(pattern) = &args[0].value {
                assert_eq!(pattern, "add <n>");
            }
        } else {
            panic!("Expected Call expression");
        }
    }
}
