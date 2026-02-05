use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn test_lower_struct() {
    let module =
        parse_and_lower("struct Point:\n    x: f64\n    y: f64\n\nfn origin() -> i64:\n    return 0\n").unwrap();

    assert!(module.types.lookup("Point").is_some());
}

#[test]
fn test_unknown_type_error() {
    let result = parse_and_lower("fn test(x: Unknown) -> i64:\n    return 0\n");

    assert!(matches!(result, Err(LowerError::UnknownType { .. })));
}

#[test]
fn test_unknown_variable_error() {
    let result = parse_and_lower("fn test() -> i64:\n    return unknown\n");

    assert!(matches!(result, Err(LowerError::UnknownVariable(_))));
}

/// E1052: Self mutation in immutable fn method should error
#[test]
fn test_self_mutation_in_fn_method_error() {
    // fn methods cannot mutate self fields
    let source = r#"
class Counter:
    count: i32

    fn increment():
        self.count = self.count + 1
"#;
    let result = parse_and_lower(source);
    assert!(
        matches!(result, Err(LowerError::SelfMutationInImmutableMethod)),
        "Self mutation in fn method should produce E1052 error"
    );
}

/// E1052: Nested self field mutation in fn method should error
#[test]
fn test_nested_self_mutation_in_fn_method_error() {
    // fn methods cannot mutate nested self fields either
    let source = r#"
struct Inner:
    value: i32

class Outer:
    inner: Inner

    fn update():
        self.inner.value = 10
"#;
    let result = parse_and_lower(source);
    assert!(
        matches!(result, Err(LowerError::SelfMutationInImmutableMethod)),
        "Nested self mutation in fn method should produce E1052 error"
    );
}

/// Self mutation in me method should work
#[test]
fn test_self_mutation_in_me_method_ok() {
    // me methods can mutate self fields
    let source = r#"
class Counter:
    count: i32

    me increment():
        self.count = self.count + 1
"#;
    let result = parse_and_lower(source);
    assert!(result.is_ok(), "Self mutation in me method should work");
}

/// Reading self in fn method should work
#[test]
fn test_self_read_in_fn_method_ok() {
    // fn methods can read self fields
    let source = r#"
class Counter:
    count: i32

    fn get_count() -> i32:
        self.count
"#;
    let result = parse_and_lower(source);
    assert!(result.is_ok(), "Reading self in fn method should work");
}
