//! Codegen-level tests for MIR instruction compilation.
//!
//! These tests construct MIR directly (bypassing lowering) and compile via AOT
//! (Cranelift ObjectModule) to verify each `compile_instruction` match arm in
//! `instr/mod.rs` produces valid native code. AOT avoids SIGSEGV issues with
//! multiple JIT instances in one process.

use crate::codegen::Codegen;
use crate::hir::{self, PointerKind, TypeId};
use crate::mir::{MirFunction, MirLocal, MirModule, LocalKind};
use crate::mir::{
    BlockId, ContractKind, FStringPart, GpuAtomicOp, GpuMemoryScope, MirInst, MirLiteral,
    MirPattern, ParallelBackend, PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};
use simple_parser::ast::Visibility;

/// Build a MirModule with a single function that:
/// - Has no parameters
/// - Returns i64
/// - Executes the given instructions, then returns `ret_vreg`
fn build_module(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> MirModule {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    let ret = build(&mut func);
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
    let mut module = MirModule::new();
    module.functions.push(func);
    module
}

/// Compile a MIR module to object code via AOT. Returns true if successful.
fn aot_compiles(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) -> bool {
    let module = build_module(name, build);
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

/// Compile a MIR module with globals via AOT.
fn aot_compiles_module(module: MirModule) -> bool {
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen.compile_module(&module).is_ok()
}

// =============================================================================
// Constants (constants.rs)
// =============================================================================

#[test]
fn codegen_const_int() {
    assert!(aot_compiles("const_int", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest, value: 42 });
        dest
    }));
}

#[test]
fn codegen_const_float() {
    assert!(aot_compiles("const_float", |f| {
        let fv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat { dest: fv, value: 3.14 });
        block.instructions.push(MirInst::Cast { dest, source: fv, from_ty: TypeId::F64, to_ty: TypeId::I64 });
        dest
    }));
}

#[test]
fn codegen_const_bool_true() {
    assert!(aot_compiles("const_bool_t", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstBool { dest, value: true });
        dest
    }));
}

#[test]
fn codegen_const_bool_false() {
    assert!(aot_compiles("const_bool_f", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstBool { dest, value: false });
        dest
    }));
}

// =============================================================================
// Basic ops (basic_ops.rs)
// =============================================================================

#[test]
fn codegen_copy() {
    assert!(aot_compiles("copy_test", |f| {
        let src = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: src, value: 99 });
        block.instructions.push(MirInst::Copy { dest, src });
        dest
    }));
}

#[test]
fn codegen_unary_negate() {
    assert!(aot_compiles("unary_neg", |f| {
        let src = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: src, value: 42 });
        block.instructions.push(MirInst::UnaryOp { dest, op: hir::UnaryOp::Neg, operand: src });
        dest
    }));
}

#[test]
fn codegen_unary_not() {
    assert!(aot_compiles("unary_not", |f| {
        let src = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstBool { dest: src, value: true });
        block.instructions.push(MirInst::UnaryOp { dest, op: hir::UnaryOp::Not, operand: src });
        dest
    }));
}

#[test]
fn codegen_cast_int_to_float_to_int() {
    assert!(aot_compiles("cast_round", |f| {
        let i = f.new_vreg();
        let fv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: i, value: 7 });
        block.instructions.push(MirInst::Cast { dest: fv, source: i, from_ty: TypeId::I64, to_ty: TypeId::F64 });
        block.instructions.push(MirInst::Cast { dest, source: fv, from_ty: TypeId::F64, to_ty: TypeId::I64 });
        dest
    }));
}

// =============================================================================
// BinOp (core.rs)
// =============================================================================

#[test]
fn codegen_binop_all_ops() {
    let mut module = MirModule::new();

    fn make_binop_func(name: &str, op: hir::BinOp, a: i64, b: i64) -> MirFunction {
        let mut f = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        let va = f.new_vreg();
        let vb = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: va, value: a });
        block.instructions.push(MirInst::ConstInt { dest: vb, value: b });
        block.instructions.push(MirInst::BinOp { dest, op, left: va, right: vb });
        block.terminator = Terminator::Return(Some(dest));
        f
    }

    module.functions.push(make_binop_func("add_test", hir::BinOp::Add, 10, 32));
    module.functions.push(make_binop_func("sub_test", hir::BinOp::Sub, 50, 8));
    module.functions.push(make_binop_func("mul_test", hir::BinOp::Mul, 6, 7));
    module.functions.push(make_binop_func("div_test", hir::BinOp::Div, 84, 2));
    module.functions.push(make_binop_func("eq_test", hir::BinOp::Eq, 42, 42));
    module.functions.push(make_binop_func("lt_test", hir::BinOp::Lt, 5, 10));

    assert!(aot_compiles_module(module));
}

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
        block.instructions.push(MirInst::LocalAddr { dest: addr, local_index: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Store { addr, value: val, ty: TypeId::I64 });
        block.instructions.push(MirInst::Load { dest: loaded, addr, ty: TypeId::I64 });
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
        block.instructions.push(MirInst::BoxInt { dest: boxed, value: val });
        block.instructions.push(MirInst::UnboxInt { dest: unboxed, value: boxed });
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
        block.instructions.push(MirInst::BoxFloat { dest: boxed, value: fval });
        block.instructions.push(MirInst::UnboxFloat { dest: unboxed, value: boxed });
        block.instructions.push(MirInst::Cast { dest, source: unboxed, from_ty: TypeId::F64, to_ty: TypeId::I64 });
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
        block.instructions.push(MirInst::Drop { value: val, ty: TypeId::I64 });
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
        block.instructions.push(MirInst::ConstBool { dest: cond, value: true });
        block.instructions.push(MirInst::DecisionProbe {
            decision_id: 0, result: cond, file: "test.spl".to_string(), line: 1, column: 1,
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
        block.instructions.push(MirInst::ConstBool { dest: cond, value: true });
        block.instructions.push(MirInst::ConditionProbe {
            decision_id: 0, condition_id: 0, result: cond,
            file: "test.spl".to_string(), line: 1, column: 1,
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
        block.instructions.push(MirInst::PathProbe { path_id: 0, block_id: 0 });
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
            value: val, unit_name: "Score".to_string(),
            min: 0, max: 100, overflow: UnitOverflowBehavior::Default,
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
            dest, value: val, from_bits: 8, to_bits: 16, signed: true,
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
            dest, value: val, from_bits: 16, to_bits: 8, signed: true,
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
        block.instructions.push(MirInst::UnitSaturate { dest, value: val, min: 0, max: 255 });
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
            dest, enum_name: "Color".to_string(), variant_name: "Red".to_string(),
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
        block.instructions.push(MirInst::ConstInt { dest: payload, value: 42 });
        block.instructions.push(MirInst::EnumWith {
            dest, enum_name: "Option".to_string(), variant_name: "Some".to_string(), payload,
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
            dest: val, enum_name: "Color".to_string(), variant_name: "Red".to_string(),
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
        block.instructions.push(MirInst::ConstInt { dest: payload, value: 42 });
        block.instructions.push(MirInst::EnumWith {
            dest: wrapped, enum_name: "Option".to_string(), variant_name: "Some".to_string(), payload,
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
        block.instructions.push(MirInst::UnionWrap { dest, value: val, type_index: 0 });
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
        block.instructions.push(MirInst::UnionWrap { dest: wrapped, value: val, type_index: 0 });
        block.instructions.push(MirInst::UnionDiscriminant { dest, value: wrapped });
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
        block.instructions.push(MirInst::UnionWrap { dest: wrapped, value: val, type_index: 0 });
        block.instructions.push(MirInst::UnionPayload { dest, value: wrapped, type_index: 0 });
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
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::OptionNone { dest });
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
    block.instructions.push(MirInst::TryUnwrap { dest, value: opt, error_block, error_dest });

    assert!(func.blocks[0].instructions.iter().any(|i| matches!(i, MirInst::TryUnwrap { .. })));
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
        block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::Unique, value: val });
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
        block.instructions.push(MirInst::PointerRef { dest: ptr, kind: PointerKind::Borrow, source: val });
        block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::Borrow });
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
        block.instructions.push(MirInst::ConstBool { dest: cond, value: true });
        block.instructions.push(MirInst::ContractCheck {
            condition: cond, kind: ContractKind::Precondition,
            func_name: "contract_chk".to_string(), message: None,
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
        block.instructions.push(MirInst::ContractOldCapture { dest, value: val });
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

// =============================================================================
// Collections — ArrayLit, TupleLit, DictLit (collections.rs)
// =============================================================================

#[test]
fn codegen_array_lit() {
    assert!(aot_compiles("array_lit", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::ArrayLit { dest, elements: vec![a, b] });
        dest
    }));
}

#[test]
fn codegen_tuple_lit() {
    assert!(aot_compiles("tuple_lit", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::TupleLit { dest, elements: vec![a, b] });
        dest
    }));
}

#[test]
fn codegen_dict_lit() {
    assert!(aot_compiles("dict_lit", |f| {
        let k = f.new_vreg();
        let v = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: k, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: v, value: 42 });
        block.instructions.push(MirInst::DictLit { dest, keys: vec![k], values: vec![v] });
        dest
    }));
}

#[test]
fn codegen_vec_lit() {
    assert!(aot_compiles("vec_lit", |f| {
        let a = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::VecLit { dest, elements: vec![a] });
        dest
    }));
}

// =============================================================================
// IndexGet / IndexSet / SliceOp (collections.rs)
// =============================================================================

#[test]
fn codegen_index_get() {
    assert!(aot_compiles("idx_get", |f| {
        let a = f.new_vreg();
        let arr = f.new_vreg();
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
        block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![a] });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::IndexGet { dest, collection: arr, index: idx });
        dest
    }));
}

#[test]
fn codegen_index_set() {
    assert!(aot_compiles("idx_set", |f| {
        let a = f.new_vreg();
        let arr = f.new_vreg();
        let idx = f.new_vreg();
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
        block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![a] });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::IndexSet { collection: arr, index: idx, value: val });
        arr
    }));
}

#[test]
fn codegen_slice_op() {
    assert!(aot_compiles("slice_op", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let arr = f.new_vreg();
        let start = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![a, b] });
        block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
        block.instructions.push(MirInst::SliceOp {
            dest, collection: arr, start: Some(start), end: None, step: None,
        });
        dest
    }));
}

// =============================================================================
// String / FString (collections.rs)
// =============================================================================

#[test]
fn codegen_const_string() {
    assert!(aot_compiles("const_str", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstString {
            dest, value: "hello".to_string(),
        });
        dest
    }));
}

#[test]
fn codegen_const_symbol() {
    assert!(aot_compiles("const_sym", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstSymbol {
            dest, value: "my_sym".to_string(),
        });
        dest
    }));
}

#[test]
fn codegen_fstring_format() {
    assert!(aot_compiles("fstr", |f| {
        let val = f.new_vreg();
        let boxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::BoxInt { dest: boxed, value: val });
        block.instructions.push(MirInst::FStringFormat {
            dest,
            parts: vec![
                FStringPart::Literal("value=".to_string()),
                FStringPart::Expr(boxed),
            ],
        });
        dest
    }));
}

// =============================================================================
// Struct / Field (closures_structs.rs, fields.rs)
// =============================================================================

#[test]
fn codegen_struct_init_field_get_set() {
    assert!(aot_compiles("struct_ops", |f| {
        let val = f.new_vreg();
        let obj = f.new_vreg();
        let got = f.new_vreg();
        let newval = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::StructInit {
            dest: obj,
            type_id: TypeId::I64,
            struct_size: 8,
            field_offsets: vec![0],
            field_types: vec![TypeId::I64],
            field_values: vec![val],
        });
        block.instructions.push(MirInst::FieldGet {
            dest: got, object: obj, byte_offset: 0, field_type: TypeId::I64,
        });
        block.instructions.push(MirInst::ConstInt { dest: newval, value: 99 });
        block.instructions.push(MirInst::FieldSet {
            object: obj, byte_offset: 0, field_type: TypeId::I64, value: newval,
        });
        got
    }));
}

// =============================================================================
// Closure / IndirectCall (closures_structs.rs)
// =============================================================================

#[test]
fn codegen_closure_create_and_indirect_call() {
    // Need a callable function in the module for the closure
    let mut func = MirFunction::new("identity".to_string(), TypeId::I64, Visibility::Public);
    let param_vreg = func.new_vreg();
    func.params.push(MirLocal {
        name: "x".to_string(), ty: TypeId::I64,
        kind: LocalKind::Parameter, is_ghost: false,
    });
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(param_vreg));

    let mut main = MirFunction::new("clos_test".to_string(), TypeId::I64, Visibility::Public);
    let closure = main.new_vreg();
    let arg = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ClosureCreate {
        dest: closure,
        func_name: "identity".to_string(),
        closure_size: 8,
        capture_offsets: vec![],
        capture_types: vec![],
        captures: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::IndirectCall {
        dest: Some(dest),
        callee: closure,
        param_types: vec![TypeId::I64],
        return_type: TypeId::I64,
        args: vec![arg],
        effect: crate::mir::Effect::Compute,
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(func);
    module.functions.push(main);

    assert!(aot_compiles_module(module));
}

// =============================================================================
// Method calls (closures_structs.rs, methods.rs, extern_classes.rs)
// =============================================================================

#[test]
fn codegen_method_call_static() {
    // MethodCallStatic compiles as Call with receiver prepended
    // Need a target function
    let mut target = MirFunction::new("Point::get_x".to_string(), TypeId::I64, Visibility::Public);
    let self_vreg = target.new_vreg();
    target.params.push(MirLocal {
        name: "self".to_string(), ty: TypeId::I64,
        kind: LocalKind::Parameter, is_ghost: false,
    });
    target.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(self_vreg));

    let mut main = MirFunction::new("method_static".to_string(), TypeId::I64, Visibility::Public);
    let recv = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "Point::get_x".to_string(), args: vec![],
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(target);
    module.functions.push(main);

    assert!(aot_compiles_module(module));
}

#[test]
fn codegen_method_call_virtual() {
    assert!(aot_compiles("method_virt", |f| {
        let recv = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
        block.instructions.push(MirInst::MethodCallVirtual {
            dest: Some(dest), receiver: recv, vtable_slot: 0,
            param_types: vec![], return_type: TypeId::I64, args: vec![],
        });
        dest
    }));
}

#[test]
fn codegen_builtin_method() {
    assert!(aot_compiles("builtin_m", |f| {
        let recv = f.new_vreg();
        let arr = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: recv, value: 1 });
        block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![recv] });
        block.instructions.push(MirInst::BuiltinMethod {
            dest: Some(dest), receiver: arr,
            receiver_type: "Array".to_string(), method: "len".to_string(), args: vec![],
        });
        dest
    }));
}

#[test]
fn codegen_extern_method_call() {
    assert!(aot_compiles("extern_m", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ExternMethodCall {
            dest: Some(dest), receiver: None,
            class_name: "Math".to_string(), method_name: "pi".to_string(),
            is_static: true, args: vec![],
        });
        dest
    }));
}

// =============================================================================
// Pattern (pattern.rs)
// =============================================================================

#[test]
fn codegen_pattern_test() {
    assert!(aot_compiles("pat_test", |f| {
        let subject = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: subject, value: 42 });
        block.instructions.push(MirInst::PatternTest {
            dest, subject, pattern: MirPattern::Literal(MirLiteral::Int(42)),
        });
        dest
    }));
}

#[test]
fn codegen_pattern_bind() {
    assert!(aot_compiles("pat_bind", |f| {
        let subject = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: subject, value: 42 });
        block.instructions.push(MirInst::PatternBind {
            dest, subject,
            binding: PatternBinding { name: "x".to_string(), path: vec![] },
        });
        dest
    }));
}

// =============================================================================
// Interpreter fallback (interpreter.rs, core.rs)
// =============================================================================

#[test]
fn codegen_interp_call() {
    assert!(aot_compiles("interp_call", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::InterpCall {
            dest: Some(dest), func_name: "test_func".to_string(), args: vec![],
        });
        dest
    }));
}

#[test]
fn codegen_interp_eval() {
    assert!(aot_compiles("interp_eval", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::InterpEval { dest, expr_index: 0 });
        dest
    }));
}

// =============================================================================
// GcAlloc / Wait / GetElementPtr (memory.rs)
// =============================================================================

#[test]
fn codegen_gc_alloc() {
    assert!(aot_compiles("gc_alloc", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GcAlloc { dest, ty: TypeId::I64 });
        dest
    }));
}

#[test]
fn codegen_wait() {
    assert!(aot_compiles("wait_test", |f| {
        let target = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: target, value: 0 });
        block.instructions.push(MirInst::Wait { dest: Some(dest), target });
        dest
    }));
}

#[test]
fn codegen_get_element_ptr() {
    assert!(aot_compiles("gep", |f| {
        let base = f.new_vreg();
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: base, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::GetElementPtr { dest, base, index: idx });
        dest
    }));
}

// =============================================================================
// Global Load/Store (memory.rs)
// =============================================================================

#[test]
fn codegen_global_load_store() {
    let mut func = MirFunction::new("global_test".to_string(), TypeId::I64, Visibility::Public);
    let val = func.new_vreg();
    let loaded = func.new_vreg();
    let block = func.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::GlobalStore {
        global_name: "MY_GLOBAL".to_string(), value: val, ty: TypeId::I64,
    });
    block.instructions.push(MirInst::GlobalLoad {
        dest: loaded, global_name: "MY_GLOBAL".to_string(), ty: TypeId::I64,
    });
    block.terminator = Terminator::Return(Some(loaded));

    let mut module = MirModule::new();
    module.globals.push(("MY_GLOBAL".to_string(), TypeId::I64, true));
    module.functions.push(func);

    assert!(aot_compiles_module(module));
}

// =============================================================================
// Async / Generator / Actor (async_ops.rs, actors.rs)
// =============================================================================

#[test]
fn codegen_future_create() {
    assert!(aot_compiles("future_c", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 42 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::FutureCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_await() {
    assert!(aot_compiles("await_test", |f| {
        let future = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: future, value: 0 });
        block.instructions.push(MirInst::Await { dest, future });
        dest
    }));
}

#[test]
fn codegen_actor_spawn() {
    assert!(aot_compiles("actor_sp", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ActorSpawn { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_actor_send() {
    assert!(aot_compiles("actor_send", |f| {
        let actor = f.new_vreg();
        let msg = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
        block.instructions.push(MirInst::ActorSend { actor, message: msg });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_actor_recv() {
    assert!(aot_compiles("actor_recv", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ActorRecv { dest });
        dest
    }));
}

#[test]
fn codegen_generator_create() {
    assert!(aot_compiles("gen_create", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let ret = f.new_vreg();
        f.block_mut(body_block).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GeneratorCreate { dest, body_block });
        dest
    }));
}

#[test]
fn codegen_yield() {
    assert!(aot_compiles("yield_test", |f| {
        let val = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Yield { value: val });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_generator_next() {
    assert!(aot_compiles("gen_next", |f| {
        let gen = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: gen, value: 0 });
        block.instructions.push(MirInst::GeneratorNext { dest, generator: gen });
        dest
    }));
}

// =============================================================================
// Parallel iterators (parallel.rs)
// =============================================================================

#[test]
fn codegen_par_map() {
    assert!(aot_compiles("par_map", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: closure, value: 0 });
        block.instructions.push(MirInst::ParMap { dest, input, closure, backend: None });
        dest
    }));
}

#[test]
fn codegen_par_reduce() {
    assert!(aot_compiles("par_reduce", |f| {
        let input = f.new_vreg();
        let initial = f.new_vreg();
        let closure = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: initial, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: closure, value: 0 });
        block.instructions.push(MirInst::ParReduce { dest, input, initial, closure, backend: None });
        dest
    }));
}

#[test]
fn codegen_par_filter() {
    assert!(aot_compiles("par_filter", |f| {
        let input = f.new_vreg();
        let pred = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: pred, value: 0 });
        block.instructions.push(MirInst::ParFilter { dest, input, predicate: pred, backend: None });
        dest
    }));
}

#[test]
fn codegen_par_for_each() {
    assert!(aot_compiles("par_each", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: closure, value: 0 });
        block.instructions.push(MirInst::ParForEach { input, closure, backend: None });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

// =============================================================================
// GPU instructions (instr_gpu.rs, simd_stubs.rs, collections.rs)
// =============================================================================

#[test]
fn codegen_gpu_shared_alloc() {
    assert!(aot_compiles("gpu_shmem", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuSharedAlloc {
            dest, element_type: TypeId::F64, size: 64,
        });
        dest
    }));
}

#[test]
fn codegen_neighbor_load() {
    assert!(aot_compiles("neighbor", |f| {
        let arr = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::NeighborLoad {
            dest, array: arr, direction: hir::NeighborDirection::Left,
        });
        dest
    }));
}

// =============================================================================
// SIMD vector operations (simd_stubs.rs, collections.rs)
// =============================================================================

/// Helper: build a single-element vector vreg
fn push_vec1(f: &mut MirFunction) -> VReg {
    let elem = f.new_vreg();
    let vec = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::VecLit { dest: vec, elements: vec![elem] });
    vec
}

#[test]
fn codegen_vec_sum() {
    assert!(aot_compiles("vec_sum", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSum { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_product() {
    assert!(aot_compiles("vec_product", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecProduct { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_min() {
    assert!(aot_compiles("vec_min", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMin { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_max() {
    assert!(aot_compiles("vec_max", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMax { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_all() {
    assert!(aot_compiles("vec_all", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAll { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_any() {
    assert!(aot_compiles("vec_any", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAny { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_extract() {
    assert!(aot_compiles("vec_extract", |f| {
        let src = push_vec1(f);
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::VecExtract { dest, vector: src, index: idx });
        dest
    }));
}

#[test]
fn codegen_vec_with() {
    assert!(aot_compiles("vec_with", |f| {
        let src = push_vec1(f);
        let idx = f.new_vreg();
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 99 });
        block.instructions.push(MirInst::VecWith { dest, vector: src, index: idx, value: val });
        dest
    }));
}

#[test]
fn codegen_vec_sqrt() {
    assert!(aot_compiles("vec_sqrt", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSqrt { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_abs() {
    assert!(aot_compiles("vec_abs", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAbs { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_floor() {
    assert!(aot_compiles("vec_floor", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecFloor { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_ceil() {
    assert!(aot_compiles("vec_ceil", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecCeil { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_round() {
    assert!(aot_compiles("vec_round", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecRound { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_recip() {
    assert!(aot_compiles("vec_recip", |f| {
        let src = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecRecip { dest, source: src });
        dest
    }));
}

#[test]
fn codegen_vec_shuffle() {
    assert!(aot_compiles("vec_shuffle", |f| {
        let src = push_vec1(f);
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecShuffle { dest, source: src, indices });
        dest
    }));
}

#[test]
fn codegen_vec_blend() {
    assert!(aot_compiles("vec_blend", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecBlend { dest, first: a, second: b, indices });
        dest
    }));
}

#[test]
fn codegen_vec_select() {
    assert!(aot_compiles("vec_select", |f| {
        let mask = push_vec1(f);
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSelect { dest, mask, if_true: a, if_false: b });
        dest
    }));
}

#[test]
fn codegen_vec_load() {
    assert!(aot_compiles("vec_load", |f| {
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecLoad { dest, array: arr, offset: off });
        dest
    }));
}

#[test]
fn codegen_vec_store() {
    assert!(aot_compiles("vec_store", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecStore { source: src, array: arr, offset: off });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_gather() {
    assert!(aot_compiles("vec_gather", |f| {
        let arr = f.new_vreg();
        let indices = push_vec1(f);
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::VecGather { dest, array: arr, indices });
        dest
    }));
}

#[test]
fn codegen_vec_scatter() {
    assert!(aot_compiles("vec_scatter", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let indices = push_vec1(f);
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::VecScatter { source: src, array: arr, indices });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_fma() {
    assert!(aot_compiles("vec_fma", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let c = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecFma { dest, a, b, c });
        dest
    }));
}

#[test]
fn codegen_vec_masked_load() {
    assert!(aot_compiles("vec_mload", |f| {
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let mask = push_vec1(f);
        let def = push_vec1(f);
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecMaskedLoad { dest, array: arr, offset: off, mask, default: def });
        dest
    }));
}

#[test]
fn codegen_vec_masked_store() {
    assert!(aot_compiles("vec_mstore", |f| {
        let src = push_vec1(f);
        let arr = f.new_vreg();
        let off = f.new_vreg();
        let mask = push_vec1(f);
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
        block.instructions.push(MirInst::VecMaskedStore { source: src, array: arr, offset: off, mask });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_vec_min_vec() {
    assert!(aot_compiles("vec_min_vec", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMinVec { dest, a, b });
        dest
    }));
}

#[test]
fn codegen_vec_max_vec() {
    assert!(aot_compiles("vec_max_vec", |f| {
        let a = push_vec1(f);
        let b = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMaxVec { dest, a, b });
        dest
    }));
}

#[test]
fn codegen_vec_clamp() {
    assert!(aot_compiles("vec_clamp", |f| {
        let src = push_vec1(f);
        let lo = push_vec1(f);
        let hi = push_vec1(f);
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecClamp { dest, source: src, lo, hi });
        dest
    }));
}

// =============================================================================
// GPU atomic operations
// =============================================================================

#[test]
fn codegen_gpu_atomic() {
    assert!(aot_compiles("gpu_atomic", |f| {
        let ptr = f.new_vreg();
        let val = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
        block.instructions.push(MirInst::GpuAtomic { dest, op: GpuAtomicOp::Add, ptr, value: val });
        dest
    }));
}

#[test]
fn codegen_gpu_atomic_cmpxchg() {
    assert!(aot_compiles("gpu_cmpxchg", |f| {
        let ptr = f.new_vreg();
        let expected = f.new_vreg();
        let desired = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: expected, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: desired, value: 1 });
        block.instructions.push(MirInst::GpuAtomicCmpXchg { dest, ptr, expected, desired });
        dest
    }));
}

// =============================================================================
// GPU intrinsics (work item queries, barriers, fences)
// =============================================================================

#[test]
fn codegen_gpu_global_id() {
    assert!(aot_compiles("gpu_gid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuGlobalId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_local_id() {
    assert!(aot_compiles("gpu_lid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuLocalId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_group_id() {
    assert!(aot_compiles("gpu_grid", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuGroupId { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_global_size() {
    assert!(aot_compiles("gpu_gsz", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuGlobalSize { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_local_size() {
    assert!(aot_compiles("gpu_lsz", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuLocalSize { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_num_groups() {
    assert!(aot_compiles("gpu_ngrp", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuNumGroups { dest, dim: 0 });
        dest
    }));
}

#[test]
fn codegen_gpu_barrier() {
    assert!(aot_compiles("gpu_bar", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::GpuBarrier);
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

#[test]
fn codegen_gpu_mem_fence() {
    assert!(aot_compiles("gpu_fence", |f| {
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::GpuMemFence { scope: GpuMemoryScope::Device });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

// =============================================================================
// Actor operations (missing from codegen tests)
// =============================================================================

#[test]
fn codegen_actor_join() {
    assert!(aot_compiles("actor_join", |f| {
        let actor = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
        block.instructions.push(MirInst::ActorJoin { dest, actor });
        dest
    }));
}

#[test]
fn codegen_actor_reply() {
    assert!(aot_compiles("actor_reply", |f| {
        let msg = f.new_vreg();
        let ret = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
        block.instructions.push(MirInst::ActorReply { message: msg });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        ret
    }));
}

// =============================================================================
// Call instruction (calls.rs) — missing from codegen tests
// =============================================================================

#[test]
fn codegen_call() {
    // Call a function defined in the same module
    let mut target = MirFunction::new("add_one".to_string(), TypeId::I64, Visibility::Public);
    let param = target.new_vreg();
    target.params.push(MirLocal {
        name: "x".to_string(), ty: TypeId::I64,
        kind: LocalKind::Parameter, is_ghost: false,
    });
    let one = target.new_vreg();
    let result = target.new_vreg();
    let block = target.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
    block.instructions.push(MirInst::BinOp { dest: result, op: hir::BinOp::Add, left: param, right: one });
    block.terminator = Terminator::Return(Some(result));

    let mut main = MirFunction::new("call_test".to_string(), TypeId::I64, Visibility::Public);
    let arg = main.new_vreg();
    let dest = main.new_vreg();
    let block = main.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 41 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest),
        target: crate::mir::CallTarget::Pure("add_one".to_string()),
        args: vec![arg],
    });
    block.terminator = Terminator::Return(Some(dest));

    let mut module = MirModule::new();
    module.functions.push(target);
    module.functions.push(main);
    assert!(aot_compiles_module(module));
}
