use simple_parser::error::ParseError;
use simple_parser::Parser;

fn parse(source: &str) -> Result<simple_parser::ast::Module, ParseError> {
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

// === Question Mark in Identifiers Tests ===
// Design Decision: `?` is NOT allowed in method names (unlike Ruby)
// The `?` character is reserved for:
// - Try operator: `result?` (error propagation)
// - Optional types: `T?` (sugar for Option<T>)
// - Future: Optional chaining `?.` and nullish coalescing `??`
//
// Use `is_*` prefix for predicates instead: is_empty(), is_valid(), is_some()

#[test]
fn test_question_mark_not_allowed_in_function_name() {
    // Function names cannot contain `?` - this should fail to parse
    // The `?` is tokenized separately from the identifier
    let result = parse("fn is_valid?() -> bool:\n    return true\n");
    // The parser will see `is_valid` as identifier, then `?` as a separate token
    // This will cause a parse error because `?` is not valid after function name
    assert!(result.is_err(), "Function names with ? should not parse");
}

#[test]
fn test_question_mark_not_allowed_in_method_name() {
    // Method names cannot contain `?`
    let result = parse(
        r#"
impl Foo:
    fn empty?() -> bool:
        return true
"#,
    );
    assert!(result.is_err(), "Method names with ? should not parse");
}

#[test]
fn test_question_mark_not_allowed_in_variable_name() {
    // Variable names cannot contain `?`
    let result = parse("val valid? = true\n");
    assert!(result.is_err(), "Variable names with ? should not parse");
}

#[test]
fn test_question_mark_valid_as_try_operator() {
    // `?` IS valid as try operator (postfix on expressions)
    let result = parse(
        r#"
fn get_value() -> Result<i64, Error>:
    val x = some_operation()?
    return Ok(x)
"#,
    );
    assert!(result.is_ok(), "Try operator ? should parse correctly");
}

#[test]
fn test_question_mark_valid_as_optional_type() {
    // `?` IS valid as optional type syntax
    let result = parse("fn get_name() -> str?:\n    return None\n");
    assert!(result.is_ok(), "Optional type ? should parse correctly");
}

#[test]
fn test_is_prefix_predicate_naming_convention() {
    // Correct predicate naming uses is_* prefix
    let result = parse(
        r#"
impl MyStruct:
    fn is_empty() -> bool:
        return true

    fn is_valid() -> bool:
        return true
"#,
    );
    assert!(result.is_ok(), "is_* prefix predicates should parse correctly");
}
