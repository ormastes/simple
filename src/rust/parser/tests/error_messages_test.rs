//! Tests for enhanced error messages (Phase 1)

use simple_parser::{Parser, ParseError};

#[test]
fn test_missing_comma_in_function_args() {
    let source = r#"
fn test():
    result(x: 10 y: 20)
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();

    assert!(result.is_err());
    let err = result.unwrap_err();
    let err_msg = format!("{}", err);

    // Should mention function arguments context
    assert!(err_msg.contains("function arguments"), "Error should mention 'function arguments' context. Got: {}", err_msg);

    // Should mention the missing comma
    assert!(err_msg.contains("comma") || err_msg.contains("Comma"), "Error should mention comma. Got: {}", err_msg);

    // Should mention the argument name
    assert!(err_msg.contains("y"), "Error should mention argument 'y'. Got: {}", err_msg);
}

#[test]
fn test_missing_comma_with_string_args() {
    let source = r#"
fn test():
    AudioSource(name: "test" volume: 1.0)
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();

    assert!(result.is_err());
    let err = result.unwrap_err();
    let err_msg = format!("{}", err);

    assert!(err_msg.contains("function arguments"), "Error should mention 'function arguments'. Got: {}", err_msg);
    assert!(err_msg.contains("volume"), "Error should mention argument 'volume'. Got: {}", err_msg);
}

#[test]
fn test_correct_function_args_parse() {
    let source = r#"
fn test():
    result(x: 10, y: 20)
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();

    // Should parse successfully with comma
    assert!(result.is_ok(), "Should parse correctly with comma: {:?}", result.err());
}

#[test]
fn test_contextual_error_type() {
    let source = r#"
fn test():
    func(a: 1 b: 2)
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();

    assert!(result.is_err());
    let err = result.unwrap_err();

    // Check if it's a ContextualSyntaxError
    match err {
        ParseError::ContextualSyntaxError { context, message, suggestion, help, .. } => {
            assert_eq!(context, "function arguments");
            assert!(message.contains("b"));
            assert!(suggestion.is_some(), "Should provide a suggestion");
            assert!(help.is_some(), "Should provide help text");

            let sugg = suggestion.unwrap();
            assert!(sugg.contains("comma") || sugg.contains("b"), "Suggestion should mention comma or 'b'. Got: {}", sugg);
        }
        _ => panic!("Expected ContextualSyntaxError, got: {:?}", err),
    }
}
