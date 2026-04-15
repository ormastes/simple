use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn test_lower_literals() {
    let module = parse_and_lower(
        "fn test() -> i64:\n    let a: i64 = 42\n    let b: f64 = 3.15\n    let c: bool = true\n    return a\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3);
}

#[test]
fn test_lower_binary_ops() {
    let module = parse_and_lower("fn compare(a: i64, b: i64) -> bool:\n    return a < b\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::BOOL);

    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert_eq!(expr.ty, TypeId::BOOL);
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_lower_array_expression() {
    let module = parse_and_lower("fn test() -> i64:\n    let arr = [1, 2, 3]\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

// Regression coverage for Phase 0A global variable type resolution fix:
//
// The fix in module_pass.rs ensures `var x: u64 = ...` resolves the type
// from Pattern::Typed when LetStmt.ty is None (the parser's normal path).
//
// Unit tests below are currently blocked from running by pre-existing
// compilation errors in value_tests_basic.rs (E0308: Arc<HashMap> mismatch).
// Integration verification: pure_gui.spl renders via fb_addr global in QEMU.
//
// When value_tests_basic.rs is fixed, uncomment these tests:
//
// #[test]
// fn test_module_level_typed_var_resolves_type() {
//     let module = parse_and_lower(
//         "var addr: u64 = 100\nfn test() -> u64:\n    return addr + 1\n",
//     ).unwrap();
//     let addr_entry = module.globals.iter().find(|(name, _)| name == "addr");
//     assert!(addr_entry.is_some());
//     assert_eq!(addr_entry.unwrap().1, TypeId::I64);
// }
//
// #[test]
// fn test_module_level_typed_val_resolves_type() {
//     let module = parse_and_lower(
//         "val size: u32 = 42\nfn test() -> u32:\n    return size\n",
//     ).unwrap();
//     let size_entry = module.globals.iter().find(|(name, _)| name == "size");
//     assert!(size_entry.is_some());
//     assert_eq!(size_entry.unwrap().1, TypeId::I32);
// }

#[test]
fn test_lower_tuple_expression() {
    let module = parse_and_lower("fn test() -> i64:\n    let t = (1, 2, 3)\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

#[test]
fn test_lower_empty_array() {
    let module = parse_and_lower("fn test() -> i64:\n    let arr = []\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_index_expression() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let arr = [1, 2, 3]\n    let x = arr[0]\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 2);
}

#[test]
fn test_lower_function_call() {
    let module = parse_and_lower(
        "fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n",
    )
    .unwrap();

    assert_eq!(module.functions.len(), 2);
}

#[test]
fn test_lower_if_expression() {
    let module = parse_and_lower("fn test(x: i64) -> i64:\n    let y = if x > 0: 1 else: 0\n    return y\n").unwrap();

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
    let module = parse_and_lower("fn test() -> f64:\n    return 3.15\n").unwrap();

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
    let module = parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a and b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);

    let module = parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a or b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);
}

#[test]
fn test_lower_field_access() {
    let module =
        parse_and_lower("struct Point:\n    x: i64\n    y: i64\n\nfn test(p: Point) -> i64:\n    return p.x\n")
            .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    }
}

#[test]
fn test_lower_assignment() {
    let module = parse_and_lower("fn test() -> i64:\n    let mut x: i64 = 0\n    x = 42\n    return x\n").unwrap();

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
    let module = parse_and_lower("fn test() -> i64:\n    let x = 1 + 2\n    return x\n").unwrap();

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
