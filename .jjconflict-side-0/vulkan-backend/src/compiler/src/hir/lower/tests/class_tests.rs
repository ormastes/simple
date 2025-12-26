use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn test_lower_struct() {
    let module = parse_and_lower(
        "struct Point:\n    x: f64\n    y: f64\n\nfn origin() -> i64:\n    return 0\n",
    )
    .unwrap();

    assert!(module.types.lookup("Point").is_some());
}

#[test]
fn test_unknown_type_error() {
    let result = parse_and_lower("fn test(x: Unknown) -> i64:\n    return 0\n");

    assert!(matches!(result, Err(LowerError::UnknownType(_))));
}

#[test]
fn test_unknown_variable_error() {
    let result = parse_and_lower("fn test() -> i64:\n    return unknown\n");

    assert!(matches!(result, Err(LowerError::UnknownVariable(_))));
}
