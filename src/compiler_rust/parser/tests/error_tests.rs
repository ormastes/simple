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
// `?` IS allowed as a suffix in function/method names (e.g., fn iter_empty?())
// This supports the Simple language convention used in iterator and other modules.
// The `?` character is also used for:
// - Try operator: `result?` (error propagation)
// - Optional types: `T?` (sugar for Option<T>)
// - Future: Optional chaining `?.` and nullish coalescing `??`

#[test]
fn test_question_mark_allowed_in_function_name() {
    // Function names CAN have a trailing `?` (e.g., fn is_valid?())
    let result = parse("fn is_valid?() -> bool:\n    return true\n");
    assert!(result.is_ok(), "Function names with ? should parse");
}

#[test]
fn test_question_mark_allowed_in_method_name() {
    // Method names CAN have a trailing `?`
    let result = parse(
        r#"
impl Foo:
    fn empty?() -> bool:
        return true
"#,
    );
    assert!(result.is_ok(), "Method names with ? should parse");
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

#[test]
fn test_lambda_brace_block_with_if() {
    let code = "fn test():\n    \\data: {\n        if true:\n            1\n        else:\n            2\n    }\n";
    let result = parse(code);
    if let Err(ref e) = result {
        eprintln!("Parse error: {}", e);
    }
    assert!(result.is_ok(), "Lambda brace block with if/else should parse");
}

#[test]
fn test_lambda_brace_block_simple() {
    // Just a brace block with a simple expression — this falls to inline expression path
    // because peek_brace_is_lambda_block only matches statement keywords, which is correct.
    // The { 42 } is parsed as a dict/expression, not a block.
    let code = "fn test():\n    \\data: {\n        var x = 42\n        x\n    }\n";
    let result = parse(code);
    if let Err(ref e) = result {
        eprintln!("Simple brace block parse error: {}", e);
    }
    assert!(
        result.is_ok(),
        "Simple lambda brace block should parse: {:?}",
        result.err()
    );
}

#[test]
fn test_lambda_brace_block_with_var() {
    // Brace block with var statement
    let code = "fn test():\n    \\data: {\n        var x = 1\n        x\n    }\n";
    let result = parse(code);
    if let Err(ref e) = result {
        eprintln!("Var brace block parse error: {}", e);
    }
    assert!(
        result.is_ok(),
        "Lambda brace block with var should parse: {:?}",
        result.err()
    );
}

#[test]
fn test_lambda_brace_block_with_for() {
    let code = "fn test():\n    \\data: {\n        for item in data:\n            print(item)\n        data\n    }\n";
    let result = parse(code);
    if let Err(ref e) = result {
        eprintln!("For brace block parse error: {}", e);
    }
    assert!(
        result.is_ok(),
        "Lambda brace block with for should parse: {:?}",
        result.err()
    );
}

#[test]
fn test_lambda_brace_block_comment_then_expr() {
    // Brace block where first significant token is an identifier (function call, not dict key)
    let code = "fn test():\n    \\data: {\n        inspect_fn(data)\n        data\n    }\n";
    let result = parse(code);
    if let Err(ref e) = result {
        eprintln!("Comment+expr brace block parse error: {}", e);
    }
    assert!(
        result.is_ok(),
        "Lambda brace block with function call should parse: {:?}",
        result.err()
    );
}
