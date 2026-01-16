use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn test_lower_simple_function() {
    let module = parse_and_lower("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

    assert_eq!(module.functions.len(), 1);
    let func = &module.functions[0];
    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 2);
    assert_eq!(func.return_type, TypeId::I64);
}

#[test]
fn test_basic_types() {
    // Test basic types: i64, str, bool, f64
    let module = parse_and_lower("fn greet(name: str) -> i64:\n    let x: i64 = 42\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params[0].ty, TypeId::STRING);
    assert_eq!(func.return_type, TypeId::I64);
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn test_lower_function_with_locals() {
    let module = parse_and_lower("fn compute(x: i64) -> i64:\n    let y: i64 = x * 2\n    return y\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 1);
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "y");
}

#[test]
fn test_multiple_functions() {
    let module = parse_and_lower(
        "fn foo() -> i64:\n    return 1\n\nfn bar() -> i64:\n    return 2\n\nfn baz() -> i64:\n    return 3\n",
    )
    .unwrap();

    assert_eq!(module.functions.len(), 3);
    assert_eq!(module.functions[0].name, "foo");
    assert_eq!(module.functions[1].name, "bar");
    assert_eq!(module.functions[2].name, "baz");
}

#[test]
fn test_function_with_multiple_params() {
    let module = parse_and_lower("fn multi(a: i64, b: f64, c: str, d: bool) -> i64:\n    return a\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 4);
    assert_eq!(func.params[0].ty, TypeId::I64);
    assert_eq!(func.params[1].ty, TypeId::F64);
    assert_eq!(func.params[2].ty, TypeId::STRING);
    assert_eq!(func.params[3].ty, TypeId::BOOL);
}
