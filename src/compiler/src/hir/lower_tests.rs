use super::*;
use simple_parser::Parser;

fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    lower(&module)
}

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
    let module =
        parse_and_lower("fn greet(name: str) -> i64:\n    let x: i64 = 42\n    return x\n")
            .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params[0].ty, TypeId::STRING);
    assert_eq!(func.return_type, TypeId::I64);
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn test_lower_function_with_locals() {
    let module =
        parse_and_lower("fn compute(x: i64) -> i64:\n    let y: i64 = x * 2\n    return y\n")
            .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 1);
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "y");
}

#[test]
fn test_lower_literals() {
    let module = parse_and_lower(
        "fn test() -> i64:\n    let a: i64 = 42\n    let b: f64 = 3.14\n    let c: bool = true\n    return a\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3);
}

#[test]
fn test_lower_binary_ops() {
    let module =
        parse_and_lower("fn compare(a: i64, b: i64) -> bool:\n    return a < b\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::BOOL);

    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert_eq!(expr.ty, TypeId::BOOL);
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_lower_if_statement() {
    let module = parse_and_lower(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
    ).unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::If { .. }));
}

#[test]
fn test_lower_while_loop() {
    let module = parse_and_lower(
        "fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n"
    ).unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[1], HirStmt::While { .. }));
}

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

#[test]
fn test_lower_array_expression() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let arr = [1, 2, 3]\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

#[test]
fn test_lower_tuple_expression() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let t = (1, 2, 3)\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

#[test]
fn test_lower_empty_array() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let arr = []\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_index_expression() {
    let module = parse_and_lower(
        "fn test() -> i64:\n    let arr = [1, 2, 3]\n    let x = arr[0]\n    return x\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 2);
}

#[test]
fn test_lower_function_call() {
    let module = parse_and_lower(
        "fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n"
    ).unwrap();

    assert_eq!(module.functions.len(), 2);
}

#[test]
fn test_lower_if_expression() {
    let module = parse_and_lower(
        "fn test(x: i64) -> i64:\n    let y = if x > 0: 1 else: 0\n    return y\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_string_literal() {
    // Use single quotes for raw string (double quotes create FStrings)
    let module = parse_and_lower("fn test() -> str:\n    return 'hello'\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::STRING);
}

#[test]
fn test_lower_bool_literal() {
    let module = parse_and_lower("fn test() -> bool:\n    return false\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::BOOL);
}

#[test]
fn test_lower_float_literal() {
    let module = parse_and_lower("fn test() -> f64:\n    return 3.14\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::F64);
}

#[test]
fn test_lower_nil_literal() {
    let module = parse_and_lower("fn test() -> i64:\n    let x = nil\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_unary_negation() {
    let module = parse_and_lower("fn test(x: i64) -> i64:\n    return -x\n").unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
    }
}

#[test]
fn test_lower_logical_not() {
    let module = parse_and_lower("fn test(x: bool) -> bool:\n    return not x\n").unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
    }
}

#[test]
fn test_lower_comparison_operators() {
    // Test all comparison operators return bool
    let ops = ["<", ">", "<=", ">=", "==", "!="];
    for op in ops {
        let source = format!("fn test(a: i64, b: i64) -> bool:\n    return a {} b\n", op);
        let module = parse_and_lower(&source).unwrap();
        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::BOOL);
    }
}

#[test]
fn test_lower_logical_operators() {
    // Test and/or return bool
    let module =
        parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a and b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);

    let module =
        parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a or b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);
}

#[test]
fn test_lower_field_access() {
    let module = parse_and_lower(
        "struct Point:\n    x: i64\n    y: i64\n\nfn test(p: Point) -> i64:\n    return p.x\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    }
}

#[test]
fn test_lower_assignment() {
    let module = parse_and_lower(
        "fn test() -> i64:\n    let mut x: i64 = 0\n    x = 42\n    return x\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[1], HirStmt::Assign { .. }));
}

#[test]
fn test_lower_expression_statement() {
    let module = parse_and_lower("fn test() -> i64:\n    1 + 2\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::Expr(_)));
}

#[test]
fn test_infer_type_from_binary_arithmetic() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let x = 1 + 2\n    return x\n").unwrap();

    let func = &module.functions[0];
    // The type should be inferred from the left operand (i64)
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn test_lower_return_without_value() {
    let module = parse_and_lower("fn test() -> i64:\n    return\n").unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::Return(None)));
}

#[test]
fn test_multiple_functions() {
    let module = parse_and_lower(
        "fn foo() -> i64:\n    return 1\n\nfn bar() -> i64:\n    return 2\n\nfn baz() -> i64:\n    return 3\n"
    ).unwrap();

    assert_eq!(module.functions.len(), 3);
    assert_eq!(module.functions[0].name, "foo");
    assert_eq!(module.functions[1].name, "bar");
    assert_eq!(module.functions[2].name, "baz");
}

#[test]
fn test_function_with_multiple_params() {
    let module =
        parse_and_lower("fn multi(a: i64, b: f64, c: str, d: bool) -> i64:\n    return a\n")
            .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 4);
    assert_eq!(func.params[0].ty, TypeId::I64);
    assert_eq!(func.params[1].ty, TypeId::F64);
    assert_eq!(func.params[2].ty, TypeId::STRING);
    assert_eq!(func.params[3].ty, TypeId::BOOL);
}
