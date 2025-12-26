use super::super::super::types::*;
use super::super::*;
use simple_parser::Parser;

fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    lower(&module)
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
fn test_gpu_global_id() {
    // Test gpu.global_id() intrinsic
    let module = parse_and_lower(
        "fn test() -> i64:\n    return gpu.global_id()\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::I64);

    // Check the return statement has a GPU intrinsic call
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GlobalId);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic for gpu.global_id(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_gpu_global_id_with_dim() {
    // Test gpu.global_id(dim) intrinsic with dimension argument
    let module = parse_and_lower(
        "fn test() -> i64:\n    return gpu.global_id(1)\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::I64);

    // Check the return statement has a GPU intrinsic call with dim argument
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GlobalId);
            assert_eq!(args.len(), 1);
            // Check dimension is an integer literal
            if let HirExprKind::Integer(dim) = &args[0].kind {
                assert_eq!(*dim, 1);
            } else {
                panic!("Expected Integer for dimension, got {:?}", args[0].kind);
            }
        } else {
            panic!("Expected GpuIntrinsic for gpu.global_id(1), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_gpu_barrier() {
    // Test gpu.barrier() intrinsic
    let module = parse_and_lower(
        "fn test():\n    gpu.barrier()\n"
    ).unwrap();

    let func = &module.functions[0];

    // Check the expression statement has a GPU barrier intrinsic
    if let HirStmt::Expr(expr) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::Barrier);
            assert!(args.is_empty());
        } else {
            panic!("Expected GpuIntrinsic for gpu.barrier(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Expr statement");
    }
}

#[test]
fn test_gpu_local_size() {
    // Test gpu.local_size() intrinsic
    let module = parse_and_lower(
        "fn test() -> i64:\n    return gpu.local_size()\n"
    ).unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::I64);

    // Check the return statement has a GPU intrinsic call
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::LocalSize);
        } else {
            panic!("Expected GpuIntrinsic for gpu.local_size(), got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Return statement");
    }
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

#[test]
fn test_gpu_atomic_add() {
    // Test GPU atomic_add intrinsic - uses i64 as raw address
    let module = parse_and_lower(
        "fn test_atomic_add(addr: i64, val: i64) -> i64:\n    return gpu.atomic_add(addr, val)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicAdd);
            assert_eq!(args.len(), 2); // addr + value
        } else {
            panic!("Expected GpuAtomicAdd intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_gpu_atomic_sub() {
    // Test GPU atomic_sub intrinsic
    let module = parse_and_lower(
        "fn test_atomic_sub(addr: i64, val: i64) -> i64:\n    return gpu.atomic_sub(addr, val)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicSub);
            assert_eq!(args.len(), 2); // addr + value
        } else {
            panic!("Expected GpuAtomicSub intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_gpu_atomic_min_max() {
    // Test GPU atomic_min intrinsic
    let module = parse_and_lower(
        "fn test_atomic_min(addr: i64, val: i64) -> i64:\n    return gpu.atomic_min(addr, val)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicMin);
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected GpuAtomicMin intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_gpu_atomic_bitwise() {
    // Test GPU atomic_and intrinsic
    let module = parse_and_lower(
        "fn test_atomic_and(addr: i64, val: i64) -> i64:\n    return gpu.atomic_and(addr, val)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicAnd);
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected GpuAtomicAnd intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_gpu_atomic_exchange() {
    // Test GPU atomic_exchange intrinsic
    let module = parse_and_lower(
        "fn test_atomic_xchg(addr: i64, val: i64) -> i64:\n    return gpu.atomic_exchange(addr, val)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicExchange);
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected GpuAtomicExchange intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_gpu_atomic_compare_exchange() {
    // Test GPU atomic_compare_exchange intrinsic
    let module = parse_and_lower(
        "fn test_atomic_cmpxchg(addr: i64, expected: i64, desired: i64) -> i64:\n    return gpu.atomic_compare_exchange(addr, expected, desired)\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GpuAtomicCompareExchange);
            assert_eq!(args.len(), 3); // addr + expected + desired
        } else {
            panic!("Expected GpuAtomicCompareExchange intrinsic");
        }
    } else {
        panic!("Expected return statement");
    }
}


// SIMD load/store tests

#[test]
fn test_simd_load() {
    // Test f32x4.load(arr, offset) static method
    let module = parse_and_lower(
        "fn test_load() -> i64:\n    let arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n    let v = f32x4.load(arr, 0)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement (after arr declaration) should be the load
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdLoad);
            assert_eq!(args.len(), 2); // array + offset
        } else {
            panic!("Expected GpuIntrinsic SimdLoad, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_gather() {
    // Test f32x4.gather(arr, indices) static method
    let module = parse_and_lower(
        "fn test_gather() -> i64:\n    let arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n    let idx = [0, 2, 4, 6]\n    let v = f32x4.gather(arr, idx)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after arr and idx) should be the gather
    if let HirStmt::Let { value: Some(value), .. } = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdGather);
            assert_eq!(args.len(), 2); // array + indices
        } else {
            panic!("Expected GpuIntrinsic SimdGather, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_store() {
    // Test v.store(arr, offset) instance method
    let module = parse_and_lower(
        "fn test_store() -> i64:\n    let arr = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    v.store(arr, 0)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after arr and v) should be the store
    if let HirStmt::Expr(expr) = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdStore);
            assert_eq!(args.len(), 3); // vector + array + offset
        } else {
            panic!("Expected GpuIntrinsic SimdStore, got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Expr statement");
    }
}

#[test]
fn test_simd_scatter() {
    // Test v.scatter(arr, indices) instance method
    let module = parse_and_lower(
        "fn test_scatter() -> i64:\n    let arr = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]\n    let idx = [0, 2, 4, 6]\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    v.scatter(arr, idx)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Fourth statement (after arr, idx, v) should be the scatter
    if let HirStmt::Expr(expr) = &func.body[3] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdScatter);
            assert_eq!(args.len(), 3); // vector + array + indices
        } else {
            panic!("Expected GpuIntrinsic SimdScatter, got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Expr statement");
    }
}

#[test]
fn test_simd_fma() {
    // Test v.fma(b, c) fused multiply-add
    let module = parse_and_lower(
        "fn test_fma() -> i64:\n    let a = vec[1.0, 2.0, 3.0, 4.0]\n    let b = vec[2.0, 2.0, 2.0, 2.0]\n    let c = vec[1.0, 1.0, 1.0, 1.0]\n    let r = a.fma(b, c)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Fourth statement should be the fma
    if let HirStmt::Let { value: Some(value), .. } = &func.body[3] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdFma);
            assert_eq!(args.len(), 3); // a, b, c
        } else {
            panic!("Expected GpuIntrinsic SimdFma, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_recip() {
    // Test v.recip() reciprocal
    let module = parse_and_lower(
        "fn test_recip() -> i64:\n    let v = vec[1.0, 2.0, 4.0, 8.0]\n    let r = v.recip()\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement should be the recip
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdRecip);
            assert_eq!(args.len(), 1); // just the vector
        } else {
            panic!("Expected GpuIntrinsic SimdRecip, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

// SIMD swizzle tests

#[test]
fn test_simd_swizzle_xyzw() {
    // Test identity swizzle v.xyzw
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.xyzw\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement should be the swizzle
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            assert_eq!(args.len(), 2); // vector + indices array
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_swizzle_broadcast() {
    // Test broadcast swizzle v.xxxx
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.xxxx\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement should be the swizzle
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            assert_eq!(args.len(), 2);
            // Check that indices array has 4 elements (for 4-lane result)
            if let HirExprKind::Array(indices) = &args[1].kind {
                assert_eq!(indices.len(), 4);
            } else {
                panic!("Expected indices array");
            }
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle");
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_swizzle_reverse() {
    // Test reverse swizzle v.wzyx
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.wzyx\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            // Check indices are [3, 2, 1, 0]
            if let HirExprKind::Array(indices) = &args[1].kind {
                assert_eq!(indices.len(), 4);
                // Verify indices values
                for (i, expected) in [3i64, 2, 1, 0].iter().enumerate() {
                    if let HirExprKind::Integer(val) = &indices[i].kind {
                        assert_eq!(*val, *expected);
                    } else {
                        panic!("Expected integer index");
                    }
                }
            } else {
                panic!("Expected indices array");
            }
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle");
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_swizzle_rgba() {
    // Test color-style swizzle v.rgba
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.rgba\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle");
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_swizzle_partial() {
    // Test partial swizzle v.xy (2 elements from 4)
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.xy\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            // Check indices array has 2 elements
            if let HirExprKind::Array(indices) = &args[1].kind {
                assert_eq!(indices.len(), 2);
            } else {
                panic!("Expected indices array");
            }
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle");
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_swizzle_single() {
    // Test single element swizzle v.x (1 element)
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.x\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let { value: Some(value), .. } = &func.body[1] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdShuffle);
            // Check indices array has 1 element
            if let HirExprKind::Array(indices) = &args[1].kind {
                assert_eq!(indices.len(), 1);
            } else {
                panic!("Expected indices array");
            }
        } else {
            panic!("Expected GpuIntrinsic SimdShuffle");
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

// SIMD masked load/store tests

#[test]
fn test_simd_masked_load() {
    // Test f32x4.load_masked(arr, offset, mask, default) static method
    let module = parse_and_lower(
        "fn test_masked_load() -> i64:\n    let arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n    let mask = vec[true, false, true, false]\n    let v = f32x4.load_masked(arr, 0, mask, 0.0)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after arr and mask) should be the masked load
    if let HirStmt::Let { value: Some(value), .. } = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdMaskedLoad);
            assert_eq!(args.len(), 4); // array + offset + mask + default
        } else {
            panic!("Expected GpuIntrinsic SimdMaskedLoad, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_masked_store() {
    // Test v.store_masked(arr, offset, mask) instance method
    let module = parse_and_lower(
        "fn test_masked_store() -> i64:\n    let arr = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let mask = vec[true, false, true, false]\n    v.store_masked(arr, 0, mask)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Fourth statement (after arr, v, mask) should be the masked store
    if let HirStmt::Expr(expr) = &func.body[3] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdMaskedStore);
            assert_eq!(args.len(), 4); // vector + array + offset + mask
        } else {
            panic!("Expected GpuIntrinsic SimdMaskedStore, got {:?}", expr.kind);
        }
    } else {
        panic!("Expected Expr statement");
    }
}

#[test]
fn test_simd_min_vec() {
    // Test a.min(b) instance method - element-wise minimum
    let module = parse_and_lower(
        "fn test_min() -> i64:\n    let a = vec[1.0, 4.0, 3.0, 8.0]\n    let b = vec[2.0, 2.0, 5.0, 5.0]\n    let result = a.min(b)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after a, b) should be the min operation
    if let HirStmt::Let { value: Some(value), .. } = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdMinVec);
            assert_eq!(args.len(), 2); // a + b
        } else {
            panic!("Expected GpuIntrinsic SimdMinVec, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_max_vec() {
    // Test a.max(b) instance method - element-wise maximum
    let module = parse_and_lower(
        "fn test_max() -> i64:\n    let a = vec[1.0, 4.0, 3.0, 8.0]\n    let b = vec[2.0, 2.0, 5.0, 5.0]\n    let result = a.max(b)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after a, b) should be the max operation
    if let HirStmt::Let { value: Some(value), .. } = &func.body[2] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdMaxVec);
            assert_eq!(args.len(), 2); // a + b
        } else {
            panic!("Expected GpuIntrinsic SimdMaxVec, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}

#[test]
fn test_simd_clamp() {
    // Test v.clamp(lo, hi) instance method - element-wise clamp
    let module = parse_and_lower(
        "fn test_clamp() -> i64:\n    let v = vec[0.5, 1.5, 2.5, 3.5]\n    let lo = vec[1.0, 1.0, 1.0, 1.0]\n    let hi = vec[2.0, 2.0, 2.0, 2.0]\n    let result = v.clamp(lo, hi)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Fourth statement (after v, lo, hi) should be the clamp operation
    if let HirStmt::Let { value: Some(value), .. } = &func.body[3] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &value.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::SimdClamp);
            assert_eq!(args.len(), 3); // v + lo + hi
        } else {
            panic!("Expected GpuIntrinsic SimdClamp, got {:?}", value.kind);
        }
    } else {
        panic!("Expected Let statement with value");
    }
}
