use crate::error::ParseError;
use crate::Parser;

fn parse(source: &str) -> Result<crate::ast::Module, ParseError> {
    let mut parser = Parser::new(source);
    parser.parse()
}

// === Error Handling Tests ===
// Note: The original parser_tests.rs didn't have dedicated error tests.
// This module is a placeholder for future error handling tests.

#[test]
fn test_parser_available() {
    // Placeholder test to ensure module compiles
    let result = parse("42");
    assert!(result.is_ok());
}
