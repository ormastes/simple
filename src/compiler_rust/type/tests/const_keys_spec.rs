// BDD Spec Tests for Const Keys Validation
// Tests compile-time dict key validation against ConstKeySet types

use simple_parser::Parser;
use simple_type::check;

fn parse_items(src: &str) -> Vec<simple_parser::ast::Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

// =============================================================================
// Const Key Set Type Parsing
// =============================================================================

#[test]
fn test_const_keys_type_parses() {
    // Given a type annotation with const_keys
    // When we parse the code
    // Then it should parse successfully

    let source = r#"
fn process(data: Dict<const_keys("host", "port"), String>):
    return 0

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    if let Err(ref e) = result {
        eprintln!("Type check error: {:?}", e);
    }
    assert!(result.is_ok(), "const_keys type should parse and check");
}

#[test]
fn test_dependent_keys_type_parses() {
    // Given a type annotation with dependent keys (name.keys)
    // When we parse the code
    // Then it should parse successfully

    let source = r#"
fn render(template: String, data: Dict<template.keys, String>):
    return 0

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_ok(), "dependent keys type should parse and check");
}

// =============================================================================
// Dict Key Validation - Valid Cases
// =============================================================================

#[test]
fn test_dict_with_valid_const_keys() {
    // Given a dict literal with keys matching const_keys
    // When we type check
    // Then it should succeed

    let source = r#"
val config: Dict<const_keys("host", "port"), String> = {
    "host": "localhost",
    "port": "8080"
}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_ok(), "dict with valid keys should type check");
}

#[test]
fn test_dict_with_partial_const_keys() {
    // Given a dict literal with subset of const_keys
    // When we type check
    // Current behavior: missing keys are reported as errors

    let source = r#"
val config: Dict<const_keys("host", "port"), String> = {
    "host": "localhost"
}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    // Validation checks for missing required keys
    assert!(result.is_err(), "missing key 'port' should be rejected");
}

// =============================================================================
// Dict Key Validation - Error Cases
// =============================================================================

#[test]
fn test_dict_with_unknown_key_error() {
    // Given a dict literal with a key not in const_keys
    // When we type check
    // Then it should fail with ConstKeyNotFound error

    let source = r#"
val config: Dict<const_keys("host", "port"), String> = {
    "host": "localhost",
    "portt": "8080"
}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_err(), "unknown key 'portt' should be rejected");
}

#[test]
fn test_dict_with_missing_key_error() {
    // Given a dict literal missing a required key
    // When we type check
    // Then it should fail with ConstKeyMissing error

    let source = r#"
val config: Dict<const_keys("host", "port"), String> = {
    "host": "localhost"
}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_err(), "missing key 'port' should be rejected");
}

// =============================================================================
// FString Dependent Keys
// =============================================================================

#[test]
fn test_fstring_with_defined_vars() {
    // Given an FString with placeholders that reference defined variables
    // When we type check
    // Then it should succeed

    let source = r#"
val name = "Alice"
val city = "Paris"
val template = "Hello {name}, welcome to {city}"

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    if let Err(ref e) = result {
        eprintln!("FString type check error: {:?}", e);
    }
    assert!(result.is_ok(), "FString with defined vars should type check");
}

#[test]
fn test_plain_string_type_check() {
    // Given a plain string (no interpolation)
    // When we type check
    // Then it should succeed

    let source = r#"
val message = "Hello World"

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_ok(), "plain string should type check");
}

// =============================================================================
// Phase 1: .with Method Tests (literals and local variables)
// =============================================================================

#[test]
fn test_fstring_with_literal_valid_keys() {
    // Given an FString literal with .with method call
    // When dict keys match the placeholders
    // Then it should type check successfully

    let source = r#"
val result = "Hello {name}".with {"name": "Alice"}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    if let Err(ref e) = result {
        eprintln!("Literal .with error: {:?}", e);
    }
    assert!(result.is_ok(), "FString literal .with valid keys should pass");
}

#[test]
fn test_fstring_with_variable_valid_keys() {
    // Given an FString stored in a variable
    // When .with is called with matching keys
    // Then it should type check successfully

    let source = r#"
val tmpl = "Welcome {user} to {city}"
val result = tmpl.with {"user": "Bob", "city": "Tokyo"}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    if let Err(ref e) = result {
        eprintln!("Variable .with error: {:?}", e);
    }
    assert!(result.is_ok(), "FString variable .with valid keys should pass");
}

#[test]
fn test_fstring_with_invalid_key() {
    // Given an FString literal with .with method call
    // When dict has a key not in placeholders
    // Then it should fail type checking

    let source = r#"
val result = "Hello {name}".with {"nam": "Alice"}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_err(), "FString .with unknown key should fail");
}

#[test]
fn test_fstring_with_missing_key() {
    // Given an FString literal with multiple placeholders
    // When .with is called with missing keys
    // Then it should fail type checking

    let source = r#"
val result = "Welcome {user} to {city}".with {"user": "Bob"}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    assert!(result.is_err(), "FString .with missing key should fail");
}

#[test]
fn test_fstring_with_multiple_placeholders() {
    // Given an FString with 3+ placeholders
    // When all keys provided correctly
    // Then it should pass

    let source = r#"
val email = "Dear {recipient}, {body} - {sender}"
val result = email.with {"recipient": "Alice", "body": "Hello", "sender": "Bob"}

main = 0
"#;

    let items = parse_items(source);
    let result = check(&items);
    if let Err(ref e) = result {
        eprintln!("Multi-placeholder .with error: {:?}", e);
    }
    assert!(result.is_ok(), "FString with multiple placeholders should pass");
}
