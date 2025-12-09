//! Parser unit tests

use simple_parser::Parser;

#[test]
fn test_parse_integer_literal() {
    let source = "main = 42";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse integer literal");
}

#[test]
fn test_parse_function_definition() {
    // Correct syntax: Python-like with colons and indentation
    let source = "fn add(a, b):\n    return a + b";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse function definition: {:?}", result.err());
}

#[test]
fn test_parse_let_binding() {
    let source = "let x = 10";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse let binding");
}

#[test]
fn test_parse_if_statement() {
    // Correct syntax: Python-like if with colon and indentation
    let source = "if x > 0:\n    y = 1";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse if statement: {:?}", result.err());
}

#[test]
fn test_parse_binary_expression() {
    let source = "main = 1 + 2 * 3";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse binary expression");
}

#[test]
fn test_parse_while_loop() {
    let source = "while x < 10:\n    x = x + 1";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse while loop: {:?}", result.err());
}
