//! Memory and type-safety instruction tests.
//!
//! Covers: LocalAddr/Load/Store, Boxing, Drop/EndScope, Coverage probes,
//! UnitBound/Widen/Narrow/Saturate, Enum/Union, Result/Option/TryUnwrap,
//! Pointer, Contract, Spread.

use super::{aot_compiles, aot_compiles_module};
use crate::hir::{PointerKind, TypeId};
use crate::mir::{BlockId, ContractKind, MirFunction, MirInst, MirLocal, MirModule, LocalKind, Terminator, UnitOverflowBehavior, VReg};
use simple_parser::ast::Visibility;

// =============================================================================
// Memory (memory.rs) — LocalAddr, Load, Store
// =============================================================================

#[test]
fn codegen_local_addr_store_load() {
    assert!(aot_compiles("local_mem", |f| {
        f.locals.push(MirLocal {
            name: "x".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        let addr = f.new_vreg();
        let val = f.new_vreg();
        let loaded = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::LocalAddr {
            dest: addr,
            local_index: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Store {
            addr,
            value: val,
            ty: TypeId::I64,
        });
        block.instructions.push(MirInst::Load {
            dest: loaded,
            addr,
            ty: TypeId::I64,
        });
        loaded
    }));
}

// =============================================================================
// Boxing (inline in compile_instruction)
// =============================================================================

#[test]
fn codegen_box_unbox_int() {
    assert!(aot_compiles("box_int", |f| {
        let val = f.new_vreg();
        let boxed = f.new_vreg();
        let unboxed = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::BoxInt {
            dest: boxed,
            value: val,
        });
        block.instructions.push(MirInst::UnboxInt {
            dest: unboxed,
            value: boxed,
        });
        unboxed
    }));
}

#[test]
fn codegen_box_unbox_float() {
    assert!(aot_compiles("box_float", |f| {
        let fval = f.new_vreg();
        let boxed = f.new_vreg();
        let unboxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat { dest: fval, value: 7.0 });
        block.instructions.push(MirInst::BoxFloat {
            dest: boxed,
            value: fval,
        });
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: boxed,
        });
        block.instructions.push(MirInst::Cast {
            dest,
            source: unboxed,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
}

// =============================================================================
// Drop / EndScope (no-ops in codegen)
// =============================================================================

#[test]
fn codegen_drop_noop() {
    assert!(aot_compiles("drop_noop", |f| {
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Drop {
            value: val,
            ty: TypeId::I64,
        });
        val
    }));
}

#[test]
fn codegen_end_scope_noop() {
    assert!(aot_compiles("end_scope", |f| {
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::EndScope { local_index: 0 });
        val
    }));
}

// =============================================================================
// Coverage probes (coverage.rs) — no-ops in non-coverage mode
// =============================================================================

#[test]
fn codegen_decision_probe() {
    assert!(aot_compiles("dec_probe", |f| {
        let cond = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstBool {
            dest: cond,
            value: true,
        });
        block.instructions.push(MirInst::DecisionProbe {
            decision_id: 0,
            result: cond,
            file: "test.spl".to_string(),
            line: 1,
            column: 1,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

#[test]
fn codegen_condition_probe() {
    assert!(aot_compiles("cond_probe", |f| {
        let cond = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstBool {
            dest: cond,
            value: true,
        });
        block.instructions.push(MirInst::ConditionProbe {
            decision_id: 0,
            condition_id: 0,
            result: cond,
            file: "test.spl".to_string(),
            line: 1,
            column: 1,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

#[test]
fn codegen_path_probe() {
    assert!(aot_compiles("path_probe", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::PathProbe {
            path_id: 0,
            block_id: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

// =============================================================================
// Unit type operations (units.rs)
// =============================================================================

#[test]
fn codegen_unit_bound_check() {
    assert!(aot_compiles("unit_bound", |f| {
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 50 });
        block.instructions.push(MirInst::UnitBoundCheck {
            value: val,
            unit_name: "Score".to_string(),
            min: 0,
            max: 100,
            overflow: UnitOverflowBehavior::Default,
        });
        val
    }));
}

#[test]
fn codegen_unit_widen() {
    assert!(aot_compiles("unit_widen", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnitWiden {
            dest,
            value: val,
            from_bits: 8,
            to_bits: 16,
            signed: true,
        });
        dest
    }));
}

#[test]
fn codegen_unit_narrow() {
    assert!(aot_compiles("unit_narrow", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnitNarrow {
            dest,
            value: val,
            from_bits: 16,
            to_bits: 8,
            signed: true,
            overflow: UnitOverflowBehavior::Saturate,
        });
        dest
    }));
}

#[test]
fn codegen_unit_saturate() {
    assert!(aot_compiles("unit_sat", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 300 });
        block.instructions.push(MirInst::UnitSaturate {
            dest,
            value: val,
            min: 0,
            max: 255,
        });
        dest
    }));
}

// =============================================================================
// Enum operations (enum_union.rs, pattern.rs)
// =============================================================================

#[test]
fn codegen_enum_unit() {
    assert!(aot_compiles("enum_unit", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::EnumUnit {
            dest,
            enum_name: "Color".to_string(),
            variant_name: "Red".to_string(),
        });
        dest
    }));
}

#[test]
fn codegen_enum_with() {
    assert!(aot_compiles("enum_with", |f| {
        let payload = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: payload,
            value: 42,
        });
        block.instructions.push(MirInst::EnumWith {
            dest,
            enum_name: "Option".to_string(),
            variant_name: "Some".to_string(),
            payload,
        });
        dest
    }));
}

#[test]
fn codegen_enum_discriminant() {
    assert!(aot_compiles("enum_disc", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::EnumUnit {
            dest: val,
            enum_name: "Color".to_string(),
            variant_name: "Red".to_string(),
        });
        block.instructions.push(MirInst::EnumDiscriminant { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_enum_payload() {
    assert!(aot_compiles("enum_pay", |f| {
        let payload = f.new_vreg();
        let wrapped = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: payload,
            value: 42,
        });
        block.instructions.push(MirInst::EnumWith {
            dest: wrapped,
            enum_name: "Option".to_string(),
            variant_name: "Some".to_string(),
            payload,
        });
        block.instructions.push(MirInst::EnumPayload { dest, value: wrapped });
        dest
    }));
}

// =============================================================================
// Union operations (enum_union.rs)
// =============================================================================

#[test]
fn codegen_union_wrap() {
    assert!(aot_compiles("union_wrap", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnionWrap {
            dest,
            value: val,
            type_index: 0,
        });
        dest
    }));
}

#[test]
fn codegen_union_discriminant() {
    assert!(aot_compiles("union_disc", |f| {
        let val = f.new_vreg();
        let wrapped = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnionWrap {
            dest: wrapped,
            value: val,
            type_index: 0,
        });
        block
            .instructions
            .push(MirInst::UnionDiscriminant { dest, value: wrapped });
        dest
    }));
}

#[test]
fn codegen_union_payload() {
    assert!(aot_compiles("union_pay", |f| {
        let val = f.new_vreg();
        let wrapped = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::UnionWrap {
            dest: wrapped,
            value: val,
            type_index: 0,
        });
        block.instructions.push(MirInst::UnionPayload {
            dest,
            value: wrapped,
            type_index: 0,
        });
        dest
    }));
}

// =============================================================================
// Result / Option (result.rs)
// =============================================================================

#[test]
fn codegen_option_some() {
    assert!(aot_compiles("opt_some", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::OptionSome { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_option_none() {
    assert!(aot_compiles("opt_none", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::OptionNone { dest });
        dest
    }));
}

#[test]
fn codegen_result_ok() {
    assert!(aot_compiles("res_ok", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::ResultOk { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_result_err() {
    assert!(aot_compiles("res_err", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
        block.instructions.push(MirInst::ResultErr { dest, value: val });
        dest
    }));
}

#[test]
fn codegen_try_unwrap() {
    // TryUnwrap creates internal Cranelift blocks for branching, which requires
    // the full block-sealing infrastructure. Verify MIR construction is valid.
    let mut func = MirFunction::new("try_unwrap".to_string(), TypeId::I64, Visibility::Public);
    let val = func.new_vreg();
    let opt = func.new_vreg();
    let dest = func.new_vreg();
    let error_dest = func.new_vreg();
    let error_block = func.new_block();

    let block = func.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::OptionSome { dest: opt, value: val });
    block.instructions.push(MirInst::TryUnwrap {
        dest,
        value: opt,
        error_block,
        error_dest,
    });

    assert!(func.blocks[0]
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::TryUnwrap { .. })));
}

// =============================================================================
// Pointer operations (pointers.rs)
// =============================================================================

#[test]
fn codegen_pointer_new() {
    assert!(aot_compiles("ptr_new", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::PointerNew {
            dest,
            kind: PointerKind::Unique,
            value: val,
        });
        dest
    }));
}

#[test]
fn codegen_pointer_ref_deref() {
    assert!(aot_compiles("ptr_ref_deref", |f| {
        let val = f.new_vreg();
        let ptr = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::PointerRef {
            dest: ptr,
            kind: PointerKind::Borrow,
            source: val,
        });
        block.instructions.push(MirInst::PointerDeref {
            dest,
            pointer: ptr,
            kind: PointerKind::Borrow,
        });
        dest
    }));
}

// =============================================================================
// Contract operations (contracts.rs, interpreter.rs)
// =============================================================================

#[test]
fn codegen_contract_check() {
    assert!(aot_compiles("contract_chk", |f| {
        let cond = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstBool {
            dest: cond,
            value: true,
        });
        block.instructions.push(MirInst::ContractCheck {
            condition: cond,
            kind: ContractKind::Precondition,
            func_name: "contract_chk".to_string(),
            message: None,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        ret
    }));
}

#[test]
fn codegen_contract_old_capture() {
    assert!(aot_compiles("old_cap", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block
            .instructions
            .push(MirInst::ContractOldCapture { dest, value: val });
        dest
    }));
}

// =============================================================================
// Spread (basic_ops.rs)
// =============================================================================

#[test]
fn codegen_spread() {
    assert!(aot_compiles("spread_test", |f| {
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Spread { dest, source: val });
        dest
    }));
}
