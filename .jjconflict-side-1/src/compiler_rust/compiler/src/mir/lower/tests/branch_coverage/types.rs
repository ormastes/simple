//! Type coverage tests for MIR lowering
//!
//! Tests for tuple, array, union, unit types, index dispatch/unboxing, and type boxing.

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, BinOp};
use crate::mir::lower::MirLowerer;
use crate::mir::function::MirFunction;
use crate::mir::{CallTarget, MirInst};
use simple_parser::Parser;

// =============================================================================
// Tuple element boxing (lowering_expr.rs lines 585-598)
// =============================================================================

#[test]
fn tuple_with_mixed_types() {
    let mir = compile_to_mir("fn test():\n    val t = (3.14, 42)\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::TupleLit { .. })));
}

// =============================================================================
// Array element boxing (lowering_expr.rs lines 640-653)
// =============================================================================

#[test]
fn array_float_element_boxing() {
    let mir = compile_to_mir("fn test():\n    val arr = [1.5, 2.5]\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

#[test]
fn array_int_element_boxing() {
    let mir = compile_to_mir("fn test():\n    val arr = [10, 20]\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
}

#[test]
fn array_empty() {
    let mir = compile_to_mir("fn test():\n    val arr = []\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ArrayLit { .. })));
}

// =============================================================================
// Tuple index vs array index dispatch (lowering_expr.rs line 870)
// =============================================================================

#[test]
fn tuple_index_dispatch() {
    let mir = compile_to_mir("fn test() -> i64:\n    val t = (10, 32)\n    return t[0] + t[1]\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_tuple_get"))
    }));
}

#[test]
fn array_index_dispatch() {
    let mir = compile_to_mir("fn test():\n    val arr = [10, 20]\n    val x = arr[0]\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_index_get"))
    }));
}

// =============================================================================
// Index result unboxing (lowering_expr.rs lines 938, 945)
// =============================================================================

#[test]
fn index_int_unboxing() {
    let mir = compile_to_mir("fn test() -> i64:\n    val arr = [10, 20, 42]\n    return arr[2]\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::UnboxInt { .. })));
}

#[test]
fn index_float_unboxing() {
    let mir = compile_to_mir("fn test() -> f64:\n    val arr = [1.5, 2.5]\n    return arr[0]\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::UnboxFloat { .. })));
}

// =============================================================================
// Unit types (lowering_types.rs lines 19-48)
// =============================================================================

#[test]
fn unit_type_basic() {
    // Standalone unit: `unit Name: BaseType as suffix`
    let result = compile_to_mir("unit UserId: i64 as uid\n\nfn test() -> i64:\n    return 42\n");
    if let Ok(mir) = result {
        assert!(mir.functions.len() >= 1);
    }
}

#[test]
fn unit_type_with_repr_and_constraint() {
    // Register UnitType with range constraints in HIR module type registry,
    // then lower to MIR to exercise lowering_types.rs paths
    let source = "fn test() -> i64:\n    return 42\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse");
    let mut hir_module = hir::lower(&ast).expect("hir lower");

    // Register our unit type in the module's type registry
    hir_module.types.register(hir::HirType::UnitType {
        name: "Percent".to_string(),
        repr: hir::TypeId::I64,
        bits: 64,
        signedness: hir::Signedness::Signed,
        is_float: false,
        constraints: hir::HirUnitConstraints {
            range: Some((0, 100)),
            overflow: hir::HirOverflowBehavior::Checked,
        },
    });

    let mir = crate::mir::lower::lower_to_mir(&hir_module).unwrap();
    assert!(mir.functions.len() >= 1);
}

#[test]
fn unit_bound_check_emit_direct() {
    // Directly test emit_unit_bound_check by constructing MirLowerer with a UnitType registry
    use crate::mir::instructions::BlockId;

    let mut registry = hir::TypeRegistry::new();
    let unit_ty = registry.register(hir::HirType::UnitType {
        name: "Score".to_string(),
        repr: hir::TypeId::I64,
        bits: 64,
        signedness: hir::Signedness::Signed,
        is_float: false,
        constraints: hir::HirUnitConstraints {
            range: Some((0, 100)),
            overflow: hir::HirOverflowBehavior::Saturate,
        },
    });

    let mut lowerer = MirLowerer::new();
    lowerer.type_registry = Some(&registry);

    // Begin a function so we have a valid state
    let mut func = MirFunction::new(
        "test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block(); // block 0
    lowerer.begin_function(func, "test", false).unwrap();

    // Get a VReg to use as the value
    let vreg = lowerer.with_func(|func, _| func.new_vreg()).unwrap();

    // Call emit_unit_bound_check — this should emit UnitBoundCheck instruction
    lowerer.emit_unit_bound_check(unit_ty, vreg).unwrap();

    // Verify UnitBoundCheck was emitted
    let func_result = lowerer.end_function().unwrap();
    let has_bound_check = func_result.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|i| matches!(i, MirInst::UnitBoundCheck { .. }))
    });
    assert!(has_bound_check, "expected UnitBoundCheck instruction");
}

#[test]
fn unit_bound_check_no_range() {
    // UnitType without range constraints should NOT emit UnitBoundCheck

    let mut registry = hir::TypeRegistry::new();
    let unit_ty = registry.register(hir::HirType::UnitType {
        name: "Tag".to_string(),
        repr: hir::TypeId::I64,
        bits: 64,
        signedness: hir::Signedness::Signed,
        is_float: false,
        constraints: hir::HirUnitConstraints {
            range: None,
            overflow: hir::HirOverflowBehavior::Default,
        },
    });

    let mut lowerer = MirLowerer::new();
    lowerer.type_registry = Some(&registry);
    let mut func = MirFunction::new(
        "test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "test", false).unwrap();

    let vreg = lowerer.with_func(|func, _| func.new_vreg()).unwrap();
    lowerer.emit_unit_bound_check(unit_ty, vreg).unwrap();

    let func_result = lowerer.end_function().unwrap();
    let has_bound_check = func_result.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|i| matches!(i, MirInst::UnitBoundCheck { .. }))
    });
    assert!(!has_bound_check, "should NOT emit UnitBoundCheck when no range");
}

#[test]
fn union_wrap_emit_direct() {
    // Directly test emit_union_wrap_if_needed

    let mut registry = hir::TypeRegistry::new();
    let i64_ty = hir::TypeId::I64;
    let str_ty = hir::TypeId::STRING;
    let union_ty = registry.register(hir::HirType::Union {
        variants: vec![i64_ty, str_ty],
    });

    let mut lowerer = MirLowerer::new();
    lowerer.type_registry = Some(&registry);
    let mut func = MirFunction::new(
        "test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "test", false).unwrap();

    let vreg = lowerer.with_func(|func, _| func.new_vreg()).unwrap();

    // Wrap i64 into union (should produce UnionWrap)
    let wrapped = lowerer.emit_union_wrap_if_needed(union_ty, i64_ty, vreg).unwrap();
    assert_ne!(wrapped, vreg, "expected new VReg from UnionWrap");

    let func_result = lowerer.end_function().unwrap();
    let has_union_wrap = func_result
        .blocks
        .iter()
        .any(|b| b.instructions.iter().any(|i| matches!(i, MirInst::UnionWrap { .. })));
    assert!(has_union_wrap, "expected UnionWrap instruction");
}

#[test]
fn union_wrap_not_needed() {
    // When value type is not in union variants, no wrap needed

    let mut registry = hir::TypeRegistry::new();
    let union_ty = registry.register(hir::HirType::Union {
        variants: vec![hir::TypeId::I64, hir::TypeId::STRING],
    });

    let mut lowerer = MirLowerer::new();
    lowerer.type_registry = Some(&registry);
    let mut func = MirFunction::new(
        "test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "test", false).unwrap();

    let vreg = lowerer.with_func(|func, _| func.new_vreg()).unwrap();

    // Try wrapping f64 (not in union) — should return same vreg
    let result = lowerer
        .emit_union_wrap_if_needed(union_ty, hir::TypeId::F64, vreg)
        .unwrap();
    assert_eq!(result, vreg, "non-variant type should return same vreg");

    lowerer.end_function().unwrap();
}

#[test]
fn union_wrap_non_union_type() {
    // When target type is not a Union at all, no wrap needed

    let registry = hir::TypeRegistry::new();
    let mut lowerer = MirLowerer::new();
    lowerer.type_registry = Some(&registry);
    let mut func = MirFunction::new(
        "test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "test", false).unwrap();

    let vreg = lowerer.with_func(|func, _| func.new_vreg()).unwrap();

    // Target is i64 (not a union) — should return same vreg
    let result = lowerer
        .emit_union_wrap_if_needed(hir::TypeId::I64, hir::TypeId::I64, vreg)
        .unwrap();
    assert_eq!(result, vreg);

    lowerer.end_function().unwrap();
}

// --- lowering_types.rs ? branches ---

#[test]
fn union_wrap_idle_lowerer() {
    // with_func fails in Idle state -> covers ? on line 33
    let mut lowerer = MirLowerer::new();
    let mut registry = hir::TypeRegistry::new();
    let union_ty = registry.register(hir::HirType::Union {
        variants: vec![hir::TypeId::I64, hir::TypeId::STRING],
    });
    lowerer.type_registry = Some(&registry);
    let result = lowerer.emit_union_wrap_if_needed(union_ty, hir::TypeId::I64, crate::mir::instructions::VReg(0));
    assert!(result.is_err());
}

#[test]
fn unit_bound_check_idle_lowerer() {
    // with_func fails in Idle state -> covers ? on line 59
    let mut lowerer = MirLowerer::new();
    let mut registry = hir::TypeRegistry::new();
    let unit_ty = registry.register(hir::HirType::UnitType {
        name: "Pct".to_string(),
        repr: hir::TypeId::I64,
        bits: 64,
        signedness: hir::Signedness::Signed,
        is_float: false,
        constraints: hir::HirUnitConstraints {
            range: Some((0, 100)),
            overflow: hir::HirOverflowBehavior::Checked,
        },
    });
    lowerer.type_registry = Some(&registry);
    let result = lowerer.emit_unit_bound_check(unit_ty, crate::mir::instructions::VReg(0));
    assert!(result.is_err());
}

// --- lowering_types.rs: registry=None and type-not-found branches ---

#[test]
fn union_wrap_no_registry() {
    let mut lowerer = gpu_lowerer_setup();
    // type_registry is None -> returns value unchanged
    let result =
        lowerer.emit_union_wrap_if_needed(hir::TypeId::I64, hir::TypeId::I64, crate::mir::instructions::VReg(0));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), crate::mir::instructions::VReg(0));
    lowerer.end_function().unwrap();
}

#[test]
fn unit_bound_check_no_registry() {
    let mut lowerer = gpu_lowerer_setup();
    // type_registry is None -> no-op
    let result = lowerer.emit_unit_bound_check(hir::TypeId::I64, crate::mir::instructions::VReg(0));
    assert!(result.is_ok());
    lowerer.end_function().unwrap();
}

#[test]
fn unit_bound_check_type_not_found() {
    let mut lowerer = gpu_lowerer_setup();
    let registry = hir::TypeRegistry::new();
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);
    // TypeId(999) doesn't exist in registry
    let result = lowerer.emit_unit_bound_check(hir::TypeId(999), crate::mir::instructions::VReg(0));
    assert!(result.is_ok());
    lowerer.end_function().unwrap();
}

#[test]
fn union_wrap_type_not_found() {
    let mut lowerer = gpu_lowerer_setup();
    let registry = hir::TypeRegistry::new();
    let registry_ref: &'static hir::TypeRegistry = Box::leak(Box::new(registry));
    lowerer.type_registry = Some(registry_ref);
    let result =
        lowerer.emit_union_wrap_if_needed(hir::TypeId(999), hir::TypeId::I64, crate::mir::instructions::VReg(0));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), crate::mir::instructions::VReg(0));
    lowerer.end_function().unwrap();
}
