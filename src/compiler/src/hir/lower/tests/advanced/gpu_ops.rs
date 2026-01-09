// GPU operation tests
//
// Tests for GPU-specific intrinsics:
// - Global/local thread indexing (gpu.global_id, gpu.local_size)
// - Synchronization (gpu.barrier)
// - Atomic operations (add, sub, min, max, and, or, xor, exchange, compare_exchange)

use super::*;

#[test]
fn test_gpu_global_id() {
    // Test gpu.global_id() intrinsic
    let module = parse_and_lower("fn test() -> i64:\n    return gpu.global_id()\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::I64);

    // Check the return statement has a GPU intrinsic call
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::GlobalId);
            assert!(args.is_empty());
        } else {
            panic!(
                "Expected GpuIntrinsic for gpu.global_id(), got {:?}",
                expr.kind
            );
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_gpu_global_id_with_dim() {
    // Test gpu.global_id(dim) intrinsic with dimension argument
    let module = parse_and_lower("fn test() -> i64:\n    return gpu.global_id(1)\n").unwrap();

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
            panic!(
                "Expected GpuIntrinsic for gpu.global_id(1), got {:?}",
                expr.kind
            );
        }
    } else {
        panic!("Expected Return statement");
    }
}

#[test]
fn test_gpu_barrier() {
    // Test gpu.barrier() intrinsic
    let module = parse_and_lower("fn test():\n    gpu.barrier()\n").unwrap();

    let func = &module.functions[0];

    // Check the expression statement has a GPU barrier intrinsic
    if let HirStmt::Expr(expr) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, args } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::Barrier);
            assert!(args.is_empty());
        } else {
            panic!(
                "Expected GpuIntrinsic for gpu.barrier(), got {:?}",
                expr.kind
            );
        }
    } else {
        panic!("Expected Expr statement");
    }
}

#[test]
fn test_gpu_local_size() {
    // Test gpu.local_size() intrinsic
    let module = parse_and_lower("fn test() -> i64:\n    return gpu.local_size()\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::I64);

    // Check the return statement has a GPU intrinsic call
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        if let HirExprKind::GpuIntrinsic { intrinsic, .. } = &expr.kind {
            assert_eq!(*intrinsic, GpuIntrinsicKind::LocalSize);
        } else {
            panic!(
                "Expected GpuIntrinsic for gpu.local_size(), got {:?}",
                expr.kind
            );
        }
    } else {
        panic!("Expected Return statement");
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
