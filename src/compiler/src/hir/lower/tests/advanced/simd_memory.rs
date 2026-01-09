// SIMD memory operation tests
//
// Tests for SIMD memory operations:
// - Load/store operations (contiguous memory access)
// - Gather/scatter operations (indexed memory access)
// - Masked load/store (conditional memory access)
// - Vector math (fma, recip)
// - Vector min/max/clamp

use super::*;

#[test]
fn test_simd_load() {
    // Test f32x4.load(arr, offset) static method
    let module = parse_and_lower(
        "fn test_load() -> i64:\n    let arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n    let v = f32x4.load(arr, 0)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement (after arr declaration) should be the load
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[2]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[3]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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

#[test]
fn test_simd_masked_load() {
    // Test f32x4.load_masked(arr, offset, mask, default) static method
    let module = parse_and_lower(
        "fn test_masked_load() -> i64:\n    let arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]\n    let mask = vec[true, false, true, false]\n    let v = f32x4.load_masked(arr, 0, mask, 0.0)\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Third statement (after arr and mask) should be the masked load
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[2]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[2]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[2]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[3]
    {
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
