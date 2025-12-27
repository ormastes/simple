//! Tests for advanced enum features
//!
//! These tests reproduce bugs in enum parsing:
//! - Named parameters in enum variants
//! - Methods inside enum blocks
//! - Union types

use simple_parser::Parser;

fn try_parse(src: &str) -> Result<(), String> {
    let mut parser = Parser::new(src);
    parser.parse().map(|_| ()).map_err(|e| format!("{:?}", e))
}

/// Test: Named parameters in enum variants
/// Bug: Parser expects Comma but finds Colon
#[test]
fn test_enum_variant_named_params() {
    let code = r#"
enum Color:
    RGB(r: Int, g: Int, b: Int)
    HSL(h: Float, s: Float, l: Float)
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse enum with named variant params: {:?}",
        result.err()
    );
}

/// Test: Positional parameters in enum variants (should work)
#[test]
fn test_enum_variant_positional_params() {
    let code = r#"
enum Color:
    RGB(Int, Int, Int)
    Name(String)
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse enum with positional variant params: {:?}",
        result.err()
    );
}

/// Test: Simple enum without parameters (baseline - should work)
#[test]
fn test_enum_simple() {
    let code = r#"
enum Status:
    Active
    Inactive
    Pending
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse simple enum: {:?}",
        result.err()
    );
}

/// Test: Methods inside enum blocks
/// Bug: Parser fails with "expected expression, found Indent"
#[test]
fn test_enum_with_methods() {
    let code = r#"
enum Status:
    Active
    Inactive

    fn is_active(self) -> Bool:
        match self:
            case Active:
                return True
            case Inactive:
                return False
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse enum with methods: {:?}",
        result.err()
    );
}

/// Test: Union types in class fields
/// Bug: Parser expects Comma but finds BitOr
#[test]
fn test_union_type_in_class() {
    let code = r#"
class Config:
    name: String
    value: String | None
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse class with union type field: {:?}",
        result.err()
    );
}

/// Test: Union types in function parameters
#[test]
fn test_union_type_in_function() {
    let code = r#"
fn process(value: String | Int | None) -> String:
    return "ok"
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse function with union type param: {:?}",
        result.err()
    );
}

/// Test: Union types in function return type
#[test]
fn test_union_type_in_return() {
    let code = r#"
fn maybe_get() -> String | None:
    return None
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse function with union return type: {:?}",
        result.err()
    );
}

/// Test: Complex enum combining all features
#[test]
fn test_enum_complex() {
    let code = r#"
enum SimpleType:
    IntType
    BoolType
    StringType
    ListType(elem: SimpleType)
    OptionType(inner: SimpleType)
    TupleType(elems: List[SimpleType])

    fn to_lean(self) -> String:
        match self:
            case IntType:
                return "Int"
            case BoolType:
                return "Bool"
            case StringType:
                return "String"
            case ListType(e):
                return "List " + e.to_lean()
            case OptionType(i):
                return "Option " + i.to_lean()
            case TupleType(es):
                return "Tuple"
"#;

    let result = try_parse(code);
    assert!(
        result.is_ok(),
        "Should parse complex enum with params and methods: {:?}",
        result.err()
    );
}
