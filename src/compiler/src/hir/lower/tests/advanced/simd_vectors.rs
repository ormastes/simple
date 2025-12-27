// SIMD vector type and operation tests
//
// Tests for SIMD vector types and basic operations:
// - vec[N, T] type annotations and literals
// - Type inference for vector literals
// - Arithmetic operations (addition, etc.)
// - Comparison operations
// - Reduction operations (sum, min, max, all, any)
// - Math operations (sqrt, abs, floor, ceil, round, etc.)
// - Element access and manipulation (extract, with)
// - Advanced operations (shuffle, blend, select)

use super::*;

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


#[test]
fn test_simd_vec_addition() {
    // Test SIMD vector addition
    let module = parse_and_lower(
        "fn test() -> i64:\n    let a = vec[1.0, 2.0, 3.0, 4.0]\n    let b = vec[5.0, 6.0, 7.0, 8.0]\n    let c = a + b\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3);

    // Check that c has a SIMD type (same as operands)
    if let Some(HirType::Simd { lanes, .. }) = module.types.get(func.locals[2].ty) {
        assert_eq!(*lanes, 4);
    } else {
        panic!("Expected Simd type for c, got {:?}", module.types.get(func.locals[2].ty));
    }
}

#[test]
fn test_simd_vec_comparison() {
    // Test SIMD vector comparison returns SIMD bool vector
    let module = parse_and_lower(
        "fn test() -> i64:\n    let a = vec[1.0, 2.0, 3.0, 4.0]\n    let b = vec[5.0, 6.0, 7.0, 8.0]\n    let mask = a < b\n    return 0\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3);

    // Check that mask has a SIMD bool type
    if let Some(HirType::Simd { lanes, element }) = module.types.get(func.locals[2].ty) {
        assert_eq!(*lanes, 4);
        assert_eq!(*element, TypeId::BOOL);
    } else {
        panic!("Expected Simd bool type for mask, got {:?}", module.types.get(func.locals[2].ty));
    }
}

#[test]
fn test_simd_vec_sum_reduction() {
    // Test SIMD vector .sum() reduction returns scalar
    let module = parse_and_lower(
        "fn test() -> f64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    return v.sum()\n"
    ).unwrap();

    let func = &module.functions[0];
    // The return type should match the element type (f64)
    assert_eq!(func.return_type, TypeId::F64);

    // Check the return statement has a GPU intrinsic call
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdSum);
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected GpuIntrinsic for sum(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_simd_vec_min_max_reduction() {
    // Test SIMD vector .min() and .max() reductions
    let module = parse_and_lower(
        "fn test() -> i64:\n    let v = vec[1, 2, 3, 4]\n    let min_val: i64 = v.min()\n    let max_val: i64 = v.max()\n    return min_val + max_val\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3); // v, min_val, max_val

    // Check min_val type is i64 (scalar element type)
    assert_eq!(func.locals[1].ty, TypeId::I64);
    assert_eq!(func.locals[2].ty, TypeId::I64);
}

#[test]
fn test_simd_vec_all_any_reduction() {
    // Test SIMD vector .all() and .any() reductions on bool vector
    let module = parse_and_lower(
        "fn test() -> bool:\n    let a = vec[1, 2, 3, 4]\n    let b = vec[0, 2, 3, 4]\n    let mask = a > b\n    return mask.any()\n"
    ).unwrap();

    let func = &module.functions[0];
    // Return type should be bool (not SIMD bool)
    assert_eq!(func.return_type, TypeId::BOOL);
}

#[test]
fn test_simd_decorator_with_bounds() {
    // Test @simd @bounds(default="return", strict=true) decorator syntax
    // This is a parser test - verifies the decorator args are parsed correctly
    use simple_parser::Parser;

    let src = r#"
@simd
@bounds(default="return", strict=true)
fn kernel(a: f32[], output: f32[]):
    return
"#;
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse failed");

    // Find the function
    assert_eq!(module.items.len(), 1);
    if let simple_parser::Node::Function(func) = &module.items[0] {
        assert_eq!(func.name, "kernel");
        assert_eq!(func.decorators.len(), 2);

        // Check @simd decorator
        if let simple_parser::Expr::Identifier(name) = &func.decorators[0].name {
            assert_eq!(name, "simd");
        }

        // Check @bounds decorator with args
        if let simple_parser::Expr::Identifier(name) = &func.decorators[1].name {
            assert_eq!(name, "bounds");
            assert!(func.decorators[1].args.is_some());
            let args = func.decorators[1].args.as_ref().unwrap();
            assert_eq!(args.len(), 2);
            // Verify named arguments
            assert_eq!(args[0].name, Some("default".to_string()));
            assert_eq!(args[1].name, Some("strict".to_string()));
        }
    } else {
        panic!("Expected Function node");
    }
}

#[test]
fn test_simd_vec_extract() {
    // Test v[idx] -> element extraction on SIMD vectors
    let module = parse_and_lower(
        "fn test() -> f64:\n    let v: vec[4, f64] = vec[1.0, 2.0, 3.0, 4.0]\n    return v[0]\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::F64);

    // Check that return has a SimdExtract intrinsic
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdExtract);
            assert_eq!(args.len(), 2);
            // First arg is the vector, second is the index
        } else {
            panic!("Expected GpuIntrinsic for v[0], got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_simd_vec_with() {
    // Test v.with(idx, val) -> new vector with lane replaced
    let module = parse_and_lower(
        "fn test() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[1.0, 2.0, 3.0, 4.0]\n    return v.with(2, 9.0)\n"
    ).unwrap();

    let func = &module.functions[0];

    // Check return has a SimdWith intrinsic
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdWith);
            assert_eq!(args.len(), 3);
            // args: vector, index, value
        } else {
            panic!("Expected GpuIntrinsic for v.with(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_simd_vec_sqrt() {
    // Test v.sqrt() -> element-wise square root
    let module = parse_and_lower(
        "fn test() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[1.0, 4.0, 9.0, 16.0]\n    return v.sqrt()\n"
    ).unwrap();

    let func = &module.functions[0];

    // Check return has a SimdSqrt intrinsic
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdSqrt);
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected GpuIntrinsic for v.sqrt(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_simd_vec_abs() {
    // Test v.abs() -> element-wise absolute value
    let module = parse_and_lower(
        "fn test() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[-1.0, 2.0, -3.0, 4.0]\n    return v.abs()\n"
    ).unwrap();

    let func = &module.functions[0];

    // Check return has a SimdAbs intrinsic
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdAbs);
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected GpuIntrinsic for v.abs(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_simd_vec_floor_ceil_round() {
    // Test v.floor(), v.ceil(), v.round()
    let module = parse_and_lower(
        "fn test_floor() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[1.2, 2.7, 3.5, 4.1]\n    return v.floor()\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdFloor);
        } else {
            panic!("Expected SimdFloor intrinsic");
        }
    }

    // Test ceil
    let module = parse_and_lower(
        "fn test_ceil() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[1.2, 2.7, 3.5, 4.1]\n    return v.ceil()\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdCeil);
        } else {
            panic!("Expected SimdCeil intrinsic");
        }
    }

    // Test round
    let module = parse_and_lower(
        "fn test_round() -> vec[4, f64]:\n    let v: vec[4, f64] = vec[1.2, 2.7, 3.5, 4.1]\n    return v.round()\n"
    ).unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdRound);
        } else {
            panic!("Expected SimdRound intrinsic");
        }
    }
}

#[test]
fn test_simd_vec_shuffle() {
    let module = parse_and_lower(
        "fn test_shuffle() -> vec[4, i32]:\n    let v: vec[4, i32] = vec[1, 2, 3, 4]\n    return v.shuffle([3, 2, 1, 0])\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            assert_eq!(args.len(), 2); // vector + indices
        } else {
            panic!("Expected SimdShuffle intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_simd_vec_blend() {
    let module = parse_and_lower(
        "fn test_blend() -> vec[4, f32]:\n    let a: vec[4, f32] = vec[1.0, 2.0, 3.0, 4.0]\n    let b: vec[4, f32] = vec[5.0, 6.0, 7.0, 8.0]\n    return a.blend(b, [0, 1, 4, 5])\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdBlend);
            assert_eq!(args.len(), 3); // vec1 + vec2 + indices
        } else {
            panic!("Expected SimdBlend intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_simd_vec_select() {
    let module = parse_and_lower(
        "fn test_select() -> vec[4, f32]:\n    let mask: vec[4, bool] = vec[true, false, true, false]\n    let a: vec[4, f32] = vec[1.0, 2.0, 3.0, 4.0]\n    let b: vec[4, f32] = vec[5.0, 6.0, 7.0, 8.0]\n    return mask.select(a, b)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[3] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdSelect);
            assert_eq!(args.len(), 3); // mask + if_true + if_false
        } else {
            panic!("Expected SimdSelect intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}
