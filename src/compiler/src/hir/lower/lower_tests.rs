use super::*;
use super::super::types::*;
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
    let module = parse_and_lower("fn test() -> i64:\n    let arr = []\n    return 0\n").unwrap();

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
    let module =
        parse_and_lower("fn test(x: i64) -> i64:\n    let y = if x > 0: 1 else: 0\n    return y\n")
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
    let module =
        parse_and_lower("fn test() -> i64:\n    let mut x: i64 = 0\n    x = 42\n    return x\n")
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

// ============================================================================
// SIMD Intrinsics Tests
// ============================================================================

#[test]
fn test_simd_this_index_intrinsic() {
    // Test this.index() intrinsic lowering for SIMD kernels
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    let i = this.index()\n    return i\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.name, "kernel");
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "i");
    assert_eq!(func.locals[0].ty, TypeId::I64);

    // Check the assignment statement
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        // Verify it's a GpuIntrinsic expression
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::SimdIndex);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_thread_index_intrinsic() {
    // Test this.thread_index() intrinsic lowering
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    let i = this.thread_index()\n    return i\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::SimdThreadIndex);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_group_index_intrinsic() {
    // Test this.group_index() intrinsic lowering
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    let i = this.group_index()\n    return i\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::SimdGroupIndex);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_left_neighbor_access() {
    // Test array.left_neighbor lowering with local array
    // Note: neighbor accessors work without @simd decorator
    let module = parse_and_lower(
        "fn kernel() -> i64:\n    let arr = [1, 2, 3, 4, 5]\n    let left = arr.left_neighbor\n    return left\n"
    ).unwrap();

    let func = &module.functions[0];
    // Check the second statement (after arr declaration)
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::NeighborAccess { direction, .. } = &value.kind {
            assert_eq!(*direction, NeighborDirection::Left);
        } else {
            panic!("Expected NeighborAccess, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_right_neighbor_access() {
    // Test array.right_neighbor lowering with local array
    // Note: neighbor accessors work without @simd decorator
    let module = parse_and_lower(
        "fn kernel() -> i64:\n    let arr = [1, 2, 3, 4, 5]\n    let right = arr.right_neighbor\n    return right\n"
    ).unwrap();

    let func = &module.functions[0];
    // Check the second statement (after arr declaration)
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::NeighborAccess { direction, .. } = &value.kind {
            assert_eq!(*direction, NeighborDirection::Right);
        } else {
            panic!("Expected NeighborAccess, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_thread_group_id() {
    // Test thread_group.id property
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    let gid = thread_group.id\n    return gid\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.name, "kernel");
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "gid");
    assert_eq!(func.locals[0].ty, TypeId::I64);

    // Check the let statement
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::GroupId);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_thread_group_size() {
    // Test thread_group.size property
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    let sz = thread_group.size\n    return sz\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::LocalSize);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_thread_group_barrier() {
    // Test thread_group.barrier() method
    let module = parse_and_lower(
        "@simd\nfn kernel() -> i64:\n    thread_group.barrier()\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    // Check the expression statement for barrier
    if let HirStmt::Expr(expr) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(intrinsic, &GpuIntrinsicKind::Barrier);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic, got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Expr statement");
    }
}


#[test]
fn test_simd_vec_type() {
    // Test vec[N, T] type annotation (without value to isolate type resolution)
    let module = parse_and_lower(
        "fn test(v: vec[4, f32]) -> i64:\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 1);
    assert_eq!(func.params[0].name, "v");

    // Check the type is Simd with 4 lanes and f32 element
    if let Some(HirType::Simd { lanes, element }) = module.types.get(func.params[0].ty) {
        assert_eq!(*lanes, 4);
        // Check element type is f32 (32-bit float)
        if let Some(HirType::Float { bits }) = module.types.get(*element) {
            assert_eq!(*bits, 32);
        } else {
            panic!("Expected Float type for element, got {:?}", module.types.get(*element));
        }
    } else {
        panic!("Expected Simd type, got {:?}", module.types.get(func.params[0].ty));
    }
}

#[test]
fn test_simd_vec_literal() {
    // Test vec[...] literal expression
    let module = parse_and_lower(
        "fn test() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "v");

    // Check the let statement has VecLiteral
    if let HirStmt::Let { value: Some(value), .. } = &func.body[0] {
        if let HirExprKind::VecLiteral(elements) = &value.kind {
            assert_eq!(elements.len(), 4);
        } else {
            panic!("Expected VecLiteral, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_vec_inferred_type() {
    // Test that vec literal infers correct SIMD type
    let module = parse_and_lower(
        "fn test() -> i64:\n    let v = vec[1, 2, 3, 4, 5, 6, 7, 8]\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    // Check the inferred type is Simd with 8 lanes
    if let Some(HirType::Simd { lanes, element }) = module.types.get(func.locals[0].ty) {
        assert_eq!(*lanes, 8);
        assert_eq!(*element, TypeId::I64);
    } else {
        panic!("Expected Simd type, got {:?}", module.types.get(func.locals[0].ty));
    }
}

