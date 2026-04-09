//! GPU lowering tests for MIR lowering
//!
//! Tests for GPU intrinsics, SIMD operations, atomics, lvalue, module path,
//! and function attribute/effect extraction.

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, GpuIntrinsicKind, HirExpr, HirExprKind};
use crate::mir::lower::MirLowerer;
use crate::mir::function::MirFunction;
use crate::mir::{CallTarget, MirInst};

// =============================================================================
// GPU lowering (lowering_gpu.rs)
// =============================================================================

#[test]
fn gpu_compute_basic() {
    // @gpu decorator triggers GPU lowering paths
    let result = compile_to_mir(
        "@gpu\nfn compute(data: [f64]) -> [f64]:\n    return data\n\nfn test():\n    val d = [1.0, 2.0]\n    val r = compute(d)\n",
    );
    if let Ok(mir) = result {
        assert!(mir.functions.len() >= 1);
    }
}

// =============================================================================
// GPU intrinsic lowering (lowering_gpu.rs)
// =============================================================================

#[test]
fn gpu_global_id_default_dim() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGlobalId { dim: 0, .. })));
}

#[test]
fn gpu_global_id_dim1() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[gpu_int_expr(1)]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGlobalId { dim: 1, .. })));
}

#[test]
fn gpu_global_id_dim2() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[gpu_int_expr(2)]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGlobalId { dim: 2, .. })));
}

#[test]
fn gpu_dim_arg_out_of_range() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[gpu_int_expr(5)]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_dim_arg_non_integer() {
    let mut lowerer = gpu_lowerer_setup();
    let non_int = HirExpr {
        kind: HirExprKind::Bool(true),
        ty: hir::TypeId::BOOL,
    };
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[non_int]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_local_id() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::LocalId, &[gpu_int_expr(0)]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuLocalId { .. })));
}

#[test]
fn gpu_group_id() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GroupId, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGroupId { .. })));
}

#[test]
fn gpu_global_size() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalSize, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGlobalSize { .. })));
}

#[test]
fn gpu_local_size() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::LocalSize, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuLocalSize { .. })));
}

#[test]
fn gpu_num_groups() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::NumGroups, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuNumGroups { .. })));
}

#[test]
fn gpu_barrier() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::Barrier, &[]);
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuBarrier)));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_mem_fence_default() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::MemFence, &[]);
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::GpuMemFence {
            scope: crate::mir::instructions::GpuMemoryScope::All
        }
    )));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_mem_fence_workgroup() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::MemFence, &[gpu_int_expr(0)]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::GpuMemFence {
            scope: crate::mir::instructions::GpuMemoryScope::WorkGroup
        }
    )));
}

#[test]
fn gpu_mem_fence_device() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::MemFence, &[gpu_int_expr(1)]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::GpuMemFence {
            scope: crate::mir::instructions::GpuMemoryScope::Device
        }
    )));
}

#[test]
fn gpu_mem_fence_non_integer_scope() {
    let mut lowerer = gpu_lowerer_setup();
    let non_int = HirExpr {
        kind: HirExprKind::Bool(true),
        ty: hir::TypeId::BOOL,
    };
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::MemFence, &[non_int]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::GpuMemFence {
            scope: crate::mir::instructions::GpuMemoryScope::All
        }
    )));
}

#[test]
fn gpu_simd_index() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdIndex, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGlobalId { dim: 0, .. })));
}

#[test]
fn gpu_simd_thread_index() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdThreadIndex, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuLocalId { dim: 0, .. })));
}

#[test]
fn gpu_simd_group_index() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdGroupIndex, &[]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::GpuGroupId { dim: 0, .. })));
}

#[test]
fn gpu_simd_sum() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSum, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecSum { .. })));
}

#[test]
fn gpu_simd_product() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdProduct, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecProduct { .. })));
}

#[test]
fn gpu_simd_min() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMin, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMin { .. })));
}

#[test]
fn gpu_simd_max() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMax, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMax { .. })));
}

#[test]
fn gpu_simd_all() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdAll, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecAll { .. })));
}

#[test]
fn gpu_simd_any() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdAny, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecAny { .. })));
}

#[test]
fn gpu_simd_extract() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdExtract, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecExtract { .. })));
}

#[test]
fn gpu_simd_with() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdWith,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecWith { .. })));
}

#[test]
fn gpu_simd_sqrt() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSqrt, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecSqrt { .. })));
}

#[test]
fn gpu_simd_abs() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdAbs, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecAbs { .. })));
}

#[test]
fn gpu_simd_floor() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdFloor, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecFloor { .. })));
}

#[test]
fn gpu_simd_ceil() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdCeil, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecCeil { .. })));
}

#[test]
fn gpu_simd_round() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdRound, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecRound { .. })));
}

#[test]
fn gpu_simd_shuffle() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdShuffle, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecShuffle { .. })));
}

#[test]
fn gpu_simd_blend() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdBlend,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecBlend { .. })));
}

#[test]
fn gpu_simd_select() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdSelect,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecSelect { .. })));
}

#[test]
fn gpu_simd_load() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdLoad, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecLoad { .. })));
}

#[test]
fn gpu_simd_store() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdStore,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecStore { .. })));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_simd_gather() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdGather, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecGather { .. })));
}

#[test]
fn gpu_simd_scatter() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdScatter,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecScatter { .. })));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_store_f64_materializes_nil_result() {
    let mut lowerer = gpu_lowerer_setup();
    let float_expr = HirExpr {
        kind: HirExprKind::Float(1.5),
        ty: hir::TypeId::F64,
    };
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::GpuStoreF64,
        &[gpu_dummy_expr(), gpu_dummy_expr(), float_expr],
    );
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::GpuStoreF64 { .. })));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_store_i64_materializes_nil_result() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::GpuStoreI64,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let result = result.unwrap();
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::GpuStoreI64 { .. })));
    assert!(gpu_result_is_materialized_nil(&func, result));
}

#[test]
fn gpu_simd_fma() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdFma,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecFma { .. })));
}

#[test]
fn gpu_simd_recip() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdRecip, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecRecip { .. })));
}

#[test]
fn gpu_simd_neighbor_left() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdNeighborLeft, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::NeighborLoad {
            direction: crate::hir::NeighborDirection::Left,
            ..
        }
    )));
}

#[test]
fn gpu_simd_neighbor_right() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdNeighborRight, &[gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i,
        MirInst::NeighborLoad {
            direction: crate::hir::NeighborDirection::Right,
            ..
        }
    )));
}

#[test]
fn gpu_simd_masked_load() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdMaskedLoad,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMaskedLoad { .. })));
}

#[test]
fn gpu_simd_masked_store() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdMaskedStore,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMaskedStore { .. })));
}

#[test]
fn gpu_simd_min_vec() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMinVec, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMinVec { .. })));
}

#[test]
fn gpu_simd_max_vec() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaxVec, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecMaxVec { .. })));
}

#[test]
fn gpu_simd_clamp() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdClamp,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::VecClamp { .. })));
}

#[test]
fn gpu_atomic_add() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicAdd, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Add, .. }
    )));
}

#[test]
fn gpu_atomic_sub() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicSub, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Sub, .. }
    )));
}

#[test]
fn gpu_atomic_min() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicMin, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Min, .. }
    )));
}

#[test]
fn gpu_atomic_max() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicMax, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Max, .. }
    )));
}

#[test]
fn gpu_atomic_and() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicAnd, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::And, .. }
    )));
}

#[test]
fn gpu_atomic_or() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicOr, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Or, .. }
    )));
}

#[test]
fn gpu_atomic_xor() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicXor, &[gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Xor, .. }
    )));
}

#[test]
fn gpu_atomic_exchange() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::GpuAtomicExchange,
        &[gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(
        i, MirInst::GpuAtomic { op: crate::mir::instructions::GpuAtomicOp::Xchg, .. }
    )));
}

#[test]
fn gpu_atomic_compare_exchange() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::GpuAtomicCompareExchange,
        &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::GpuAtomicCmpXchg { .. })));
}

// =============================================================================
// GPU: remaining uncovered branches
// =============================================================================

#[test]
fn gpu_dim_arg_negative() {
    // Covers: *n >= 0 being false (line 373)
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GlobalId, &[gpu_int_expr(-1)]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}
