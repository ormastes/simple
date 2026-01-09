// SIMD swizzle operation tests
//
// Tests for SIMD vector swizzling (component shuffling):
// - Identity swizzle (xyzw)
// - Broadcast swizzle (xxxx)
// - Reverse swizzle (wzyx)
// - Color-style swizzle (rgba)
// - Partial swizzle (xy, x)

use super::*;

#[test]
fn test_simd_swizzle_xyzw() {
    // Test identity swizzle v.xyzw
    let module = parse_and_lower(
        "fn test_swizzle() -> i64:\n    let v = vec[1.0, 2.0, 3.0, 4.0]\n    let r = v.xyzw\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    // Second statement should be the swizzle
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
    if let HirStmt::Let {
        value: Some(value), ..
    } = &func.body[1]
    {
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
