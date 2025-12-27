// SIMD intrinsics tests - thread indexing and thread group operations
//
// Tests for SIMD-specific intrinsics:
// - this.index(), this.thread_index(), this.group_index()
// - neighbor access (left_neighbor, right_neighbor)
// - thread_group.id, thread_group.size, thread_group.barrier()

use super::*;

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
