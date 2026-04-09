//! GPU error propagation tests for MIR lowering
//!
//! Tests for ? operator error paths in GPU intrinsic lowering, lvalue lowering,
//! module path, and function attribute/effect extraction.

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, GpuIntrinsicKind, HirExpr, HirExprKind};
use crate::mir::lower::MirLowerer;
use crate::mir::function::MirFunction;
use crate::mir::{CallTarget, MirInst};

// =============================================================================
// lower_lvalue (lowering_gpu.rs)
// =============================================================================

#[test]
fn lvalue_local() {
    let mut lowerer = gpu_lowerer_setup();
    let expr = HirExpr {
        kind: HirExprKind::Local(0),
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::LocalAddr { .. })));
}

#[test]
fn lvalue_field_access() {
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Local(0),
        ty: hir::TypeId::I64,
    });
    let expr = HirExpr {
        kind: HirExprKind::FieldAccess {
            receiver,
            field_index: 1,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::GetElementPtr { .. })));
}

#[test]
fn lvalue_index() {
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Integer(0),
        ty: hir::TypeId::I64,
    });
    let index = Box::new(HirExpr {
        kind: HirExprKind::Integer(1),
        ty: hir::TypeId::I64,
    });
    let expr = HirExpr {
        kind: HirExprKind::Index { receiver, index },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(|i| matches!(i, MirInst::GetElementPtr { .. })));
}

#[test]
fn lvalue_global() {
    let mut lowerer = gpu_lowerer_setup();
    let expr = HirExpr {
        kind: HirExprKind::Global("my_global".to_string()),
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_ok());
    let func = lowerer.end_function().unwrap();
    assert!(func.blocks.iter().flat_map(|b| &b.instructions).any(
        |i| matches!(i, MirInst::Call { target: CallTarget::Io(name), .. } if name.contains("__get_global_my_global"))
    ));
}

#[test]
fn lvalue_unsupported() {
    let mut lowerer = gpu_lowerer_setup();
    let expr = HirExpr {
        kind: HirExprKind::Integer(42),
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

// =============================================================================
// current_module_path (lowering_gpu.rs)
// =============================================================================

#[test]
fn module_path_no_file() {
    let lowerer = MirLowerer::new();
    assert_eq!(lowerer.current_module_path(), "");
}

#[test]
fn module_path_with_file() {
    let mut lowerer = MirLowerer::new();
    lowerer.current_file = Some("app/domain/user.spl".to_string());
    assert_eq!(lowerer.current_module_path(), "app.domain.user");
}

#[test]
fn module_path_windows_separators() {
    let mut lowerer = MirLowerer::new();
    lowerer.current_file = Some("app\\domain\\user.spl".to_string());
    assert_eq!(lowerer.current_module_path(), "app.domain.user");
}

// =============================================================================
// extract_function_attributes / extract_function_effects (lowering_gpu.rs)
// =============================================================================

#[test]
fn extract_attrs_inject() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: true,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert!(attrs.contains(&"inject".to_string()));
    assert!(attrs.contains(&"actor".to_string()));
}

#[test]
fn extract_attrs_pure() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: true,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::LockBase,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert!(attrs.contains(&"pure".to_string()));
    assert!(attrs.contains(&"lock_base".to_string()));
}

#[test]
fn extract_attrs_unsafe_mode() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Unsafe,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert!(attrs.contains(&"unsafe".to_string()));
}

#[test]
fn extract_effects_actor_adds_async() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec!["io".to_string()],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let effects = lowerer.extract_function_effects(&func);
    assert!(effects.contains(&"io".to_string()));
    assert!(effects.contains(&"async".to_string()));
}

#[test]
fn extract_effects_lock_base_no_async() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::LockBase,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec!["io".to_string()],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let effects = lowerer.extract_function_effects(&func);
    assert!(effects.contains(&"io".to_string()));
    assert!(!effects.contains(&"async".to_string()));
}

// =============================================================================
// GPU: lower_expr errors propagate via ? operator
// =============================================================================

#[test]
fn gpu_simd_extract_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdExtract, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_extract_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdExtract, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_with_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdWith,
        &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_with_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdWith,
        &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()],
    );
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_with_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(
        GpuIntrinsicKind::SimdWith,
        &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()],
    );
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_shuffle_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdShuffle, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_shuffle_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdShuffle, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_blend_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdBlend, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_blend_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdBlend, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_blend_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdBlend, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_select_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSelect, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_select_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSelect, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_select_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSelect, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_load_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdLoad, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_load_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdLoad, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_store_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdStore, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_store_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdStore, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_store_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdStore, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_gather_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdGather, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_gather_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdGather, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_scatter_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdScatter, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_scatter_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdScatter, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_scatter_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdScatter, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_fma_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdFma, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_fma_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdFma, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_fma_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdFma, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_neighbor_left_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdNeighborLeft, &[failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_neighbor_right_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdNeighborRight, &[failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_load_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedLoad, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_load_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedLoad, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_load_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedLoad, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_load_fourth_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedLoad, &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_store_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedStore, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_store_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedStore, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_store_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedStore, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_masked_store_fourth_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMaskedStore, &[gpu_dummy_expr(), gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_clamp_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdClamp, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_clamp_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdClamp, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_clamp_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdClamp, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_atomic_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicAdd, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_atomic_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicAdd, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_atomic_cmpxchg_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicCompareExchange, &[failing_expr(), gpu_dummy_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_atomic_cmpxchg_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicCompareExchange, &[gpu_dummy_expr(), failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_atomic_cmpxchg_third_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::GpuAtomicCompareExchange, &[gpu_dummy_expr(), gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

// Unary ops error propagation (simd_unary_op! macro)
#[test]
fn gpu_simd_sum_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdSum, &[failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_recip_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdRecip, &[failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

// Binary ops error propagation (simd_binary_op! macro)
#[test]
fn gpu_simd_min_vec_first_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMinVec, &[failing_expr(), gpu_dummy_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn gpu_simd_min_vec_second_arg_err() {
    let mut lowerer = gpu_lowerer_setup();
    let result = lowerer.lower_gpu_intrinsic(GpuIntrinsicKind::SimdMinVec, &[gpu_dummy_expr(), failing_expr()]);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

// --- lower_lvalue error propagation ---

#[test]
fn lvalue_field_access_receiver_err() {
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(HirExpr {
        kind: HirExprKind::Integer(42),
        ty: hir::TypeId::I64,
    });
    let expr = HirExpr {
        kind: HirExprKind::FieldAccess {
            receiver,
            field_index: 0,
        },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_index_receiver_err() {
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(failing_expr());
    let index = Box::new(gpu_dummy_expr());
    let expr = HirExpr {
        kind: HirExprKind::Index { receiver, index },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}

#[test]
fn lvalue_index_index_err() {
    let mut lowerer = gpu_lowerer_setup();
    let receiver = Box::new(gpu_dummy_expr());
    let index = Box::new(failing_expr());
    let expr = HirExpr {
        kind: HirExprKind::Index { receiver, index },
        ty: hir::TypeId::I64,
    };
    let result = lowerer.lower_lvalue(&expr);
    assert!(result.is_err());
    lowerer.end_function().unwrap();
}
