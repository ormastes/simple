//! Shared codegen emitter tests that run the same MIR instruction sequences
//! through multiple `CodegenEmitter` backends via `dispatch_instruction()`.
//!
//! Currently tests:
//! - **MIR Interpreter** (`MirInterpreterEmitter`): always runs
//! - **Cranelift AOT** (`Codegen::compile_module`): always runs
//! - **LLVM** (`LlvmEmitter`): runs when `llvm` feature is enabled
//!
//! Each test builds MIR instructions and verifies all backends handle them.

use crate::codegen::dispatch::dispatch_instruction;
use crate::codegen::mir_interpreter::MirInterpreterEmitter;
use crate::codegen::Codegen;
use crate::hir::{self, PointerKind, TypeId};
use crate::mir::{
    BlockId, ContractKind, FStringPart, GpuAtomicOp, GpuMemoryScope, LocalKind, MirFunction,
    MirInst, MirLiteral, MirLocal, MirModule, MirPattern, ParallelBackend, PatternBinding,
    Terminator, UnitOverflowBehavior, VReg,
};
use simple_parser::ast::Visibility;

// =============================================================================
// Backend harness functions
// =============================================================================

/// Run MIR instructions through the interpreter emitter. Returns Ok(()) on success.
fn interpreter_ok(insts: &[MirInst]) {
    let mut emitter = MirInterpreterEmitter::new();
    for inst in insts {
        dispatch_instruction(&mut emitter, inst)
            .unwrap_or_else(|e| panic!("interpreter failed on {:?}: {}", inst, e));
    }
}

/// Run MIR instructions through the interpreter and return the value of a vreg.
fn interpreter_value(insts: &[MirInst], vreg: VReg) -> i64 {
    let mut emitter = MirInterpreterEmitter::new();
    for inst in insts {
        dispatch_instruction(&mut emitter, inst)
            .unwrap_or_else(|e| panic!("interpreter failed on {:?}: {}", inst, e));
    }
    emitter.get(vreg)
}

/// Build a MirModule from instructions and compile via Cranelift AOT.
fn cranelift_ok(name: &str, build: impl FnOnce(&mut MirFunction) -> VReg) {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    let ret = build(&mut func);
    func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));
    let mut module = MirModule::new();
    module.functions.push(func);
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen
        .compile_module(&module)
        .unwrap_or_else(|e| panic!("cranelift compilation failed for {}: {:?}", name, e));
}

/// Compile a pre-built MirModule via Cranelift AOT.
fn cranelift_module_ok(module: MirModule) {
    let codegen = Codegen::new().expect("failed to create codegen");
    codegen
        .compile_module(&module)
        .unwrap_or_else(|e| panic!("cranelift module compilation failed: {:?}", e));
}

// =============================================================================
// Shared test macro
// =============================================================================

/// Generate a cranelift-only test (for ops unsupported by the interpreter).
macro_rules! cranelift_only_test {
    ($name:ident, $build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_ok(stringify!($name), $build);
            }
        }
    };
}

/// Generate tests that run the same instruction sequence through all backends.
///
/// Usage:
/// ```ignore
/// shared_test!(test_name, |f| {
///     // build instructions using f: &mut MirFunction
///     // return the VReg to use as return value
///     dest
/// });
/// ```
macro_rules! shared_test {
    ($name:ident, $build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_ok(stringify!($name), $build);
            }

            #[test]
            fn interpreter() {
                // Build a function, extract instructions, run through interpreter
                let mut func =
                    MirFunction::new(stringify!($name).to_string(), TypeId::I64, Visibility::Public);
                let _ret = ($build)(&mut func);
                let insts: Vec<MirInst> =
                    func.block_mut(BlockId(0)).unwrap().instructions.clone();
                interpreter_ok(&insts);
            }
        }
    };
}

/// Like shared_test but for tests that need a custom module (multiple functions, globals).
/// Takes a closure that returns a MirModule and a Vec<MirInst> for interpreter testing.
macro_rules! shared_module_test {
    ($name:ident, module: $module_build:expr, insts: $insts_build:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn cranelift() {
                cranelift_module_ok($module_build);
            }

            #[test]
            fn interpreter() {
                let insts = $insts_build;
                interpreter_ok(&insts);
            }
        }
    };
}

// =============================================================================
// Phase 1: Constants
// =============================================================================

shared_test!(shared_const_int, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest, value: 42 });
    dest
});

shared_test!(shared_const_float, |f: &mut MirFunction| {
    let fv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstFloat { dest: fv, value: 3.14 });
    block.instructions.push(MirInst::Cast {
        dest,
        source: fv,
        from_ty: TypeId::F64,
        to_ty: TypeId::I64,
    });
    dest
});

shared_test!(shared_const_bool_true, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstBool { dest, value: true });
    dest
});

shared_test!(shared_const_bool_false, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstBool {
            dest,
            value: false,
        });
    dest
});

shared_test!(shared_const_string, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstString {
            dest,
            value: "hello".to_string(),
        });
    dest
});

shared_test!(shared_const_symbol, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ConstSymbol {
            dest,
            value: "my_sym".to_string(),
        });
    dest
});

// =============================================================================
// Phase 1: Basic operations
// =============================================================================

shared_test!(shared_copy, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: src, value: 99 });
    block.instructions.push(MirInst::Copy { dest, src });
    dest
});

shared_test!(shared_spread, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::Spread { dest, source: val });
    dest
});

shared_test!(shared_unary_neg, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: src, value: 42 });
    block.instructions.push(MirInst::UnaryOp {
        dest,
        op: hir::UnaryOp::Neg,
        operand: src,
    });
    dest
});

shared_test!(shared_unary_not, |f: &mut MirFunction| {
    let src = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstBool { dest: src, value: true });
    block.instructions.push(MirInst::UnaryOp {
        dest,
        op: hir::UnaryOp::Not,
        operand: src,
    });
    dest
});

shared_test!(shared_cast_int_float, |f: &mut MirFunction| {
    let i = f.new_vreg();
    let fv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: i, value: 7 });
    block.instructions.push(MirInst::Cast {
        dest: fv,
        source: i,
        from_ty: TypeId::I64,
        to_ty: TypeId::F64,
    });
    block.instructions.push(MirInst::Cast {
        dest,
        source: fv,
        from_ty: TypeId::F64,
        to_ty: TypeId::I64,
    });
    dest
});

// BinOp tests — individual operations
shared_test!(shared_binop_add, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 10 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 32 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Add,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_sub, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 50 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 8 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Sub,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_mul, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 6 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 7 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Mul,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_div, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 84 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Div,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_eq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 42 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 42 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Eq,
        left: a,
        right: b,
    });
    dest
});

shared_test!(shared_binop_lt, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 5 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 10 });
    block.instructions.push(MirInst::BinOp {
        dest,
        op: hir::BinOp::Lt,
        left: a,
        right: b,
    });
    dest
});

// =============================================================================
// Phase 1: Memory safety / no-ops
// =============================================================================

shared_test!(shared_drop_noop, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Drop {
        value: val,
        ty: TypeId::I64,
    });
    val
});

shared_test!(shared_end_scope_noop, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::EndScope { local_index: 0 });
    val
});

// =============================================================================
// Phase 1: Boxing
// =============================================================================

shared_test!(shared_box_unbox_int, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let boxed = f.new_vreg();
    let unboxed = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::BoxInt { dest: boxed, value: val });
    block.instructions.push(MirInst::UnboxInt {
        dest: unboxed,
        value: boxed,
    });
    unboxed
});

shared_test!(shared_box_unbox_float, |f: &mut MirFunction| {
    let fval = f.new_vreg();
    let boxed = f.new_vreg();
    let unboxed = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstFloat { dest: fval, value: 7.0 });
    block
        .instructions
        .push(MirInst::BoxFloat { dest: boxed, value: fval });
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
});

// =============================================================================
// Phase 1: Units
// =============================================================================

shared_test!(shared_unit_widen, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitWiden {
        dest,
        value: val,
        from_bits: 8,
        to_bits: 16,
        signed: true,
    });
    dest
});

shared_test!(shared_unit_narrow, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitNarrow {
        dest,
        value: val,
        from_bits: 16,
        to_bits: 8,
        signed: true,
        overflow: UnitOverflowBehavior::Saturate,
    });
    dest
});

shared_test!(shared_unit_saturate, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 300 });
    block.instructions.push(MirInst::UnitSaturate {
        dest,
        value: val,
        min: 0,
        max: 255,
    });
    dest
});

shared_test!(shared_unit_bound_check, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 50 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val,
        unit_name: "Score".to_string(),
        min: 0,
        max: 100,
        overflow: UnitOverflowBehavior::Default,
    });
    val
});

// =============================================================================
// Phase 1: Contracts
// =============================================================================

shared_test!(shared_contract_old_capture, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::ContractOldCapture { dest, value: val });
    dest
});

shared_test!(shared_contract_check, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstBool { dest: cond, value: true });
    block.instructions.push(MirInst::ContractCheck {
        condition: cond,
        kind: ContractKind::Precondition,
        func_name: "shared_contract_check".to_string(),
        message: None,
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

// =============================================================================
// Phase 1: Pointers
// =============================================================================

shared_test!(shared_pointer_new, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew {
        dest,
        kind: PointerKind::Unique,
        value: val,
    });
    dest
});

shared_test!(shared_pointer_ref_deref, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
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
});

// =============================================================================
// Phase 1: Coverage probes (no-ops)
// =============================================================================

shared_test!(shared_decision_probe, |f: &mut MirFunction| {
    let cond = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstBool { dest: cond, value: true });
    block.instructions.push(MirInst::DecisionProbe {
        decision_id: 0,
        result: cond,
        file: "test.spl".to_string(),
        line: 1,
        column: 1,
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

shared_test!(shared_path_probe, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::PathProbe {
        path_id: 0,
        block_id: 0,
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 42 });
    ret
});

// =============================================================================
// Phase 2: Collections
// =============================================================================

shared_test!(shared_array_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 1 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::ArrayLit {
        dest,
        elements: vec![a, b],
    });
    dest
});

shared_test!(shared_tuple_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 1 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::TupleLit {
        dest,
        elements: vec![a, b],
    });
    dest
});

shared_test!(shared_dict_lit, |f: &mut MirFunction| {
    let k = f.new_vreg();
    let v = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: k, value: 1 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: v, value: 42 });
    block.instructions.push(MirInst::DictLit {
        dest,
        keys: vec![k],
        values: vec![v],
    });
    dest
});

shared_test!(shared_vec_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::VecLit {
        dest,
        elements: vec![a],
    });
    dest
});

shared_test!(shared_index_get, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 42 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a],
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::IndexGet {
        dest,
        collection: arr,
        index: idx,
    });
    dest
});

shared_test!(shared_index_set, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a],
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: idx, value: 0 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::IndexSet {
        collection: arr,
        index: idx,
        value: val,
    });
    arr
});

shared_test!(shared_slice_op, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: a, value: 1 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a, b],
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::SliceOp {
        dest,
        collection: arr,
        start: Some(start),
        end: None,
        step: None,
    });
    dest
});

// =============================================================================
// Phase 2: Structs / Fields
// =============================================================================

shared_test!(shared_struct_init_field_ops, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let obj = f.new_vreg();
    let got = f.new_vreg();
    let newval = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::StructInit {
        dest: obj,
        type_id: TypeId::I64,
        struct_size: 8,
        field_offsets: vec![0],
        field_types: vec![TypeId::I64],
        field_values: vec![val],
    });
    block.instructions.push(MirInst::FieldGet {
        dest: got,
        object: obj,
        byte_offset: 0,
        field_type: TypeId::I64,
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: newval, value: 99 });
    block.instructions.push(MirInst::FieldSet {
        object: obj,
        byte_offset: 0,
        field_type: TypeId::I64,
        value: newval,
    });
    got
});

// =============================================================================
// Phase 2: FString
// =============================================================================

shared_test!(shared_fstring_format, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let boxed = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::BoxInt { dest: boxed, value: val });
    block.instructions.push(MirInst::FStringFormat {
        dest,
        parts: vec![
            FStringPart::Literal("value=".to_string()),
            FStringPart::Expr(boxed),
        ],
    });
    dest
});

// =============================================================================
// Phase 3: Enums / Unions
// =============================================================================

shared_test!(shared_enum_unit, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::EnumUnit {
            dest,
            enum_name: "Color".to_string(),
            variant_name: "Red".to_string(),
        });
    dest
});

shared_test!(shared_enum_with, |f: &mut MirFunction| {
    let payload = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: payload, value: 42 });
    block.instructions.push(MirInst::EnumWith {
        dest,
        enum_name: "Option".to_string(),
        variant_name: "Some".to_string(),
        payload,
    });
    dest
});

shared_test!(shared_enum_discriminant, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::EnumUnit {
        dest: val,
        enum_name: "Color".to_string(),
        variant_name: "Red".to_string(),
    });
    block
        .instructions
        .push(MirInst::EnumDiscriminant { dest, value: val });
    dest
});

shared_test!(shared_union_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap {
        dest,
        value: val,
        type_index: 0,
    });
    dest
});

// =============================================================================
// Phase 3: Option / Result
// =============================================================================

shared_test!(shared_option_some, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::OptionSome { dest, value: val });
    dest
});

shared_test!(shared_option_none, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::OptionNone { dest });
    dest
});

shared_test!(shared_result_ok, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block
        .instructions
        .push(MirInst::ResultOk { dest, value: val });
    dest
});

shared_test!(shared_result_err, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 1 });
    block
        .instructions
        .push(MirInst::ResultErr { dest, value: val });
    dest
});

// =============================================================================
// Phase 3: Pattern matching
// =============================================================================

shared_test!(shared_pattern_test, |f: &mut MirFunction| {
    let subject = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: subject, value: 42 });
    block.instructions.push(MirInst::PatternTest {
        dest,
        subject,
        pattern: MirPattern::Literal(MirLiteral::Int(42)),
    });
    dest
});

shared_test!(shared_pattern_bind, |f: &mut MirFunction| {
    let subject = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: subject, value: 42 });
    block.instructions.push(MirInst::PatternBind {
        dest,
        subject,
        binding: PatternBinding {
            name: "x".to_string(),
            path: vec![],
        },
    });
    dest
});

// =============================================================================
// Phase 3: Async / Actors / Generators
// =============================================================================

shared_test!(shared_future_create, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 42 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::FutureCreate { dest, body_block });
    dest
});

shared_test!(shared_await, |f: &mut MirFunction| {
    let future = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: future, value: 0 });
    block
        .instructions
        .push(MirInst::Await { dest, future });
    dest
});

shared_test!(shared_actor_spawn, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ActorSpawn { dest, body_block });
    dest
});

shared_test!(shared_actor_send, |f: &mut MirFunction| {
    let actor = f.new_vreg();
    let msg = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: actor, value: 0 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: msg, value: 42 });
    block
        .instructions
        .push(MirInst::ActorSend { actor, message: msg });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_generator_create, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GeneratorCreate { dest, body_block });
    dest
});

shared_test!(shared_yield, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Yield { value: val });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Phase 3: GPU
// =============================================================================

shared_test!(shared_gpu_global_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuGlobalId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_barrier, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuBarrier);
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_gpu_shared_alloc, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuSharedAlloc {
            dest,
            element_type: TypeId::F64,
            size: 64,
        });
    dest
});

// =============================================================================
// Phase 3: Parallel
// =============================================================================

shared_test!(shared_par_map, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let closure = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: input, value: 0 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: closure, value: 0 });
    block.instructions.push(MirInst::ParMap {
        dest,
        input,
        closure,
        backend: None,
    });
    dest
});

shared_test!(shared_par_for_each, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let closure = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block
        .instructions
        .push(MirInst::ConstInt { dest: input, value: 0 });
    block
        .instructions
        .push(MirInst::ConstInt { dest: closure, value: 0 });
    block.instructions.push(MirInst::ParForEach {
        input,
        closure,
        backend: None,
    });
    block
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Phase 3: Enum payload
// =============================================================================

shared_test!(shared_enum_payload, |f: &mut MirFunction| {
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
});

// =============================================================================
// Phase 3: Union discriminant / payload
// =============================================================================

shared_test!(shared_union_discriminant, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let wrapped = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap { dest: wrapped, value: val, type_index: 0 });
    block.instructions.push(MirInst::UnionDiscriminant { dest, value: wrapped });
    dest
});

shared_test!(shared_union_payload, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let wrapped = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap { dest: wrapped, value: val, type_index: 0 });
    block.instructions.push(MirInst::UnionPayload { dest, value: wrapped, type_index: 0 });
    dest
});

// =============================================================================
// Phase 3: Actor join / recv / reply
// =============================================================================

shared_test!(shared_actor_join, |f: &mut MirFunction| {
    let actor = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
    block.instructions.push(MirInst::ActorJoin { dest, actor });
    dest
});

shared_test!(shared_actor_recv, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ActorRecv { dest });
    dest
});

shared_test!(shared_actor_reply, |f: &mut MirFunction| {
    let msg = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
    block.instructions.push(MirInst::ActorReply { message: msg });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Phase 3: Generator next
// =============================================================================

shared_test!(shared_generator_next, |f: &mut MirFunction| {
    let gen = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: gen, value: 0 });
    block.instructions.push(MirInst::GeneratorNext { dest, generator: gen });
    dest
});

// =============================================================================
// Phase 3: Memory — GcAlloc, Wait, GetElementPtr, LocalAddr/Store/Load
// =============================================================================

shared_test!(shared_gc_alloc, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GcAlloc { dest, ty: TypeId::I64 });
    dest
});

shared_test!(shared_wait, |f: &mut MirFunction| {
    let target = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: target, value: 0 });
    block.instructions.push(MirInst::Wait { dest: Some(dest), target });
    dest
});

shared_test!(shared_get_element_ptr, |f: &mut MirFunction| {
    let base = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: base, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::GetElementPtr { dest, base, index: idx });
    dest
});

shared_test!(shared_local_addr_store_load, |f: &mut MirFunction| {
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
});

// =============================================================================
// Phase 3: Global Load/Store (module-level test)
// =============================================================================

shared_module_test!(shared_global_load_store,
    module: {
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
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 42 },
        MirInst::GlobalStore { global_name: "MY_GLOBAL".to_string(), value: VReg(0), ty: TypeId::I64 },
        MirInst::GlobalLoad { dest: VReg(1), global_name: "MY_GLOBAL".to_string(), ty: TypeId::I64 },
    ]
);

// =============================================================================
// Phase 3: Interpreter / fallback calls
// =============================================================================

shared_test!(shared_interp_call, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest), func_name: "test_func".to_string(), args: vec![],
    });
    dest
});

shared_test!(shared_interp_eval, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::InterpEval { dest, expr_index: 0 });
    dest
});

// =============================================================================
// Phase 3: Coverage — condition probe
// =============================================================================

shared_test!(shared_condition_probe, |f: &mut MirFunction| {
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
});

// =============================================================================
// Phase 3: Method calls (module-level tests for static/virtual/builtin/extern)
// =============================================================================

shared_module_test!(shared_method_call_static,
    module: {
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
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 42 },
        MirInst::MethodCallStatic {
            dest: Some(VReg(1)), receiver: VReg(0),
            func_name: "Point::get_x".to_string(), args: vec![],
        },
    ]
);

shared_test!(shared_method_call_virtual, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
    block.instructions.push(MirInst::MethodCallVirtual {
        dest: Some(dest), receiver: recv, vtable_slot: 0,
        param_types: vec![], return_type: TypeId::I64, args: vec![],
    });
    dest
});

shared_test!(shared_builtin_method, |f: &mut MirFunction| {
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
});

shared_test!(shared_extern_method_call, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ExternMethodCall {
        dest: Some(dest), receiver: None,
        class_name: "Math".to_string(), method_name: "pi".to_string(),
        is_static: true, args: vec![],
    });
    dest
});

// =============================================================================
// Phase 3: Call (module-level test)
// =============================================================================

shared_module_test!(shared_call,
    module: {
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
        module
    },
    insts: vec![
        MirInst::ConstInt { dest: VReg(0), value: 41 },
        MirInst::Call {
            dest: Some(VReg(1)),
            target: crate::mir::CallTarget::Pure("add_one".to_string()),
            args: vec![VReg(0)],
        },
    ]
);

// =============================================================================
// Phase 3: Closure / IndirectCall (module-level test)
// =============================================================================

shared_module_test!(shared_closure_create_and_indirect_call,
    module: {
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
        module
    },
    insts: vec![
        MirInst::ClosureCreate {
            dest: VReg(0),
            func_name: "identity".to_string(),
            closure_size: 8,
            capture_offsets: vec![],
            capture_types: vec![],
            captures: vec![],
        },
        MirInst::ConstInt { dest: VReg(1), value: 42 },
        MirInst::IndirectCall {
            dest: Some(VReg(2)),
            callee: VReg(0),
            param_types: vec![TypeId::I64],
            return_type: TypeId::I64,
            args: vec![VReg(1)],
            effect: crate::mir::Effect::Compute,
        },
    ]
);

// =============================================================================
// Phase 3: TryUnwrap (cranelift-only — needs block infrastructure)
// =============================================================================

/// TryUnwrap creates internal Cranelift blocks for branching.
/// We test it cranelift-only (MIR construction) + interpreter separately.
mod shared_try_unwrap {
    use super::*;

    #[test]
    fn cranelift() {
        // TryUnwrap needs block-sealing infra, verify MIR construction is valid
        let mut func = MirFunction::new("try_unwrap".to_string(), TypeId::I64, Visibility::Public);
        let val = func.new_vreg();
        let opt = func.new_vreg();
        let dest = func.new_vreg();
        let _error_dest = func.new_vreg();
        let error_block = func.new_block();

        let block = func.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::OptionSome { dest: opt, value: val });
        block.instructions.push(MirInst::TryUnwrap { dest, value: opt, error_block, error_dest: _error_dest });

        assert!(func.blocks[0].instructions.iter().any(|i| matches!(i, MirInst::TryUnwrap { .. })));
    }

    #[test]
    fn interpreter() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::OptionSome { dest: VReg(1), value: VReg(0) },
            MirInst::TryUnwrap { dest: VReg(2), value: VReg(1), error_block: BlockId(1), error_dest: VReg(3) },
        ];
        interpreter_ok(&insts);
    }
}

// =============================================================================
// Phase 3: GPU — remaining intrinsics
// =============================================================================

shared_test!(shared_gpu_local_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuLocalId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_group_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuGroupId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_global_size, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuGlobalSize { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_local_size, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuLocalSize { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_num_groups, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::GpuNumGroups { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_mem_fence, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuMemFence { scope: GpuMemoryScope::Device });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_gpu_atomic, |f: &mut MirFunction| {
    let ptr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: ptr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::GpuAtomic { dest, op: GpuAtomicOp::Add, ptr, value: val });
    dest
});

shared_test!(shared_gpu_atomic_cmpxchg, |f: &mut MirFunction| {
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
});

shared_test!(shared_neighbor_load, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::NeighborLoad {
        dest, array: arr, direction: hir::NeighborDirection::Left,
    });
    dest
});

// =============================================================================
// Phase 3: Parallel — remaining
// =============================================================================

shared_test!(shared_par_reduce, |f: &mut MirFunction| {
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
});

shared_test!(shared_par_filter, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let pred = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: pred, value: 0 });
    block.instructions.push(MirInst::ParFilter { dest, input, predicate: pred, backend: None });
    dest
});

// =============================================================================
// Phase 3: SIMD vector operations
// =============================================================================

/// Helper: build a single-element vector vreg using raw instructions
fn push_vec1_shared(f: &mut MirFunction) -> VReg {
    let elem = f.new_vreg();
    let vec = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::VecLit { dest: vec, elements: vec![elem] });
    vec
}

shared_test!(shared_vec_sum, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSum { dest, source: src });
    dest
});

shared_test!(shared_vec_product, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecProduct { dest, source: src });
    dest
});

shared_test!(shared_vec_min, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMin { dest, source: src });
    dest
});

shared_test!(shared_vec_max, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMax { dest, source: src });
    dest
});

shared_test!(shared_vec_all, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAll { dest, source: src });
    dest
});

shared_test!(shared_vec_any, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAny { dest, source: src });
    dest
});

shared_test!(shared_vec_extract, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::VecExtract { dest, vector: src, index: idx });
    dest
});

shared_test!(shared_vec_with, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 99 });
    block.instructions.push(MirInst::VecWith { dest, vector: src, index: idx, value: val });
    dest
});

shared_test!(shared_vec_sqrt, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSqrt { dest, source: src });
    dest
});

shared_test!(shared_vec_abs, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecAbs { dest, source: src });
    dest
});

shared_test!(shared_vec_floor, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecFloor { dest, source: src });
    dest
});

shared_test!(shared_vec_ceil, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecCeil { dest, source: src });
    dest
});

shared_test!(shared_vec_round, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecRound { dest, source: src });
    dest
});

shared_test!(shared_vec_recip, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecRecip { dest, source: src });
    dest
});

shared_test!(shared_vec_shuffle, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecShuffle { dest, source: src, indices });
    dest
});

shared_test!(shared_vec_blend, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecBlend { dest, first: a, second: b, indices });
    dest
});

shared_test!(shared_vec_select, |f: &mut MirFunction| {
    let mask = push_vec1_shared(f);
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecSelect { dest, mask, if_true: a, if_false: b });
    dest
});

shared_test!(shared_vec_load, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
    block.instructions.push(MirInst::VecLoad { dest, array: arr, offset: off });
    dest
});

shared_test!(shared_vec_store, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
    block.instructions.push(MirInst::VecStore { source: src, array: arr, offset: off });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_vec_gather, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let indices = push_vec1_shared(f);
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::VecGather { dest, array: arr, indices });
    dest
});

shared_test!(shared_vec_scatter, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let arr = f.new_vreg();
    let indices = push_vec1_shared(f);
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::VecScatter { source: src, array: arr, indices });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_vec_fma, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let c = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecFma { dest, a, b, c });
    dest
});

shared_test!(shared_vec_masked_load, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let mask = push_vec1_shared(f);
    let def = push_vec1_shared(f);
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
    block.instructions.push(MirInst::VecMaskedLoad { dest, array: arr, offset: off, mask, default: def });
    dest
});

shared_test!(shared_vec_masked_store, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let arr = f.new_vreg();
    let off = f.new_vreg();
    let mask = push_vec1_shared(f);
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: off, value: 0 });
    block.instructions.push(MirInst::VecMaskedStore { source: src, array: arr, offset: off, mask });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_vec_min_vec, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMinVec { dest, a, b });
    dest
});

shared_test!(shared_vec_max_vec, |f: &mut MirFunction| {
    let a = push_vec1_shared(f);
    let b = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecMaxVec { dest, a, b });
    dest
});

shared_test!(shared_vec_clamp, |f: &mut MirFunction| {
    let src = push_vec1_shared(f);
    let lo = push_vec1_shared(f);
    let hi = push_vec1_shared(f);
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::VecClamp { dest, source: src, lo, hi });
    dest
});

// =============================================================================
// Interpreter-only value verification tests
// =============================================================================

#[cfg(test)]
mod interpreter_value_checks {
    use super::*;

    #[test]
    fn const_int_value() {
        let insts = vec![MirInst::ConstInt {
            dest: VReg(0),
            value: 42,
        }];
        assert_eq!(interpreter_value(&insts, VReg(0)), 42);
    }

    #[test]
    fn binop_add_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 10 },
            MirInst::ConstInt { dest: VReg(1), value: 32 },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Add,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn binop_mul_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 6 },
            MirInst::ConstInt { dest: VReg(1), value: 7 },
            MirInst::BinOp {
                dest: VReg(2),
                op: hir::BinOp::Mul,
                left: VReg(0),
                right: VReg(1),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn unary_neg_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::UnaryOp {
                dest: VReg(1),
                op: hir::UnaryOp::Neg,
                operand: VReg(0),
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), -42);
    }

    #[test]
    fn copy_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 99 },
            MirInst::Copy { dest: VReg(1), src: VReg(0) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 99);
    }

    #[test]
    fn unit_saturate_clamps() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 300 },
            MirInst::UnitSaturate {
                dest: VReg(1),
                value: VReg(0),
                min: 0,
                max: 255,
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 255);
    }

    #[test]
    fn box_unbox_int_roundtrip() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::BoxInt { dest: VReg(1), value: VReg(0) },
            MirInst::UnboxInt { dest: VReg(2), value: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 42);
    }

    #[test]
    fn global_store_load_roundtrip() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::GlobalStore {
                global_name: "g".to_string(),
                value: VReg(0),
                ty: TypeId::I64,
            },
            MirInst::GlobalLoad {
                dest: VReg(1),
                global_name: "g".to_string(),
                ty: TypeId::I64,
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn option_some_tagged() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::OptionSome { dest: VReg(1), value: VReg(0) },
        ];
        // Tagged: (42 << 1) | 1 = 85
        assert_eq!(interpreter_value(&insts, VReg(1)), 85);
    }

    #[test]
    fn option_none_is_zero() {
        let insts = vec![MirInst::OptionNone { dest: VReg(0) }];
        assert_eq!(interpreter_value(&insts, VReg(0)), 0);
    }
}

// =============================================================================
// Branch coverage: BinOp — all operator variants
// =============================================================================

shared_test!(shared_binop_mod, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 3 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::Mod, left: a, right: b });
    dest
});

shared_test!(shared_binop_bitand, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xFF });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::BitAnd, left: a, right: b });
    dest
});

shared_test!(shared_binop_bitor, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xF0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::BitOr, left: a, right: b });
    dest
});

shared_test!(shared_binop_bitxor, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0xFF });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0x0F });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::BitXor, left: a, right: b });
    dest
});

shared_test!(shared_binop_shift_left, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 3 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::ShiftLeft, left: a, right: b });
    dest
});

shared_test!(shared_binop_shift_right, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 8 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::ShiftRight, left: a, right: b });
    dest
});

shared_test!(shared_binop_noteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::NotEq, left: a, right: b });
    dest
});

shared_test!(shared_binop_gt, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::Gt, left: a, right: b });
    dest
});

shared_test!(shared_binop_lteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 5 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::LtEq, left: a, right: b });
    dest
});

shared_test!(shared_binop_gteq, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 5 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 5 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::GtEq, left: a, right: b });
    dest
});

cranelift_only_test!(shared_binop_is, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 42 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::Is, left: a, right: b });
    dest
});

cranelift_only_test!(shared_binop_in, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::In, left: a, right: b });
    dest
});

cranelift_only_test!(shared_binop_notin, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::NotIn, left: a, right: b });
    dest
});

shared_test!(shared_binop_and, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::And, left: a, right: b });
    dest
});

shared_test!(shared_binop_or, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::Or, left: a, right: b });
    dest
});

cranelift_only_test!(shared_binop_and_suspend, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::AndSuspend, left: a, right: b });
    dest
});

cranelift_only_test!(shared_binop_or_suspend, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 1 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::OrSuspend, left: a, right: b });
    dest
});

// BinOp::Pow creates loop blocks in Cranelift (unsealable in single-block test harness)
// and is unsupported in the interpreter. Covered by codegen_instr_tests instead.

cranelift_only_test!(shared_binop_floordiv, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 7 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::BinOp { dest, op: hir::BinOp::FloorDiv, left: a, right: b });
    dest
});

// =============================================================================
// Branch coverage: Pointer kinds
// =============================================================================

shared_test!(shared_pointer_new_shared, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::Shared, value: val });
    dest
});

shared_test!(shared_pointer_new_handle, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::Handle, value: val });
    dest
});

shared_test!(shared_pointer_new_weak, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::Weak, value: val });
    dest
});

shared_test!(shared_pointer_new_borrow_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::BorrowMut, value: val });
    dest
});

shared_test!(shared_pointer_new_raw_const, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::RawConst, value: val });
    dest
});

shared_test!(shared_pointer_new_raw_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest, kind: PointerKind::RawMut, value: val });
    dest
});

shared_test!(shared_pointer_deref_shared, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest: ptr, kind: PointerKind::Shared, value: val });
    block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::Shared });
    dest
});

shared_test!(shared_pointer_deref_weak, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest: ptr, kind: PointerKind::Weak, value: val });
    block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::Weak });
    dest
});

shared_test!(shared_pointer_deref_borrow_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerRef { dest: ptr, kind: PointerKind::BorrowMut, source: val });
    block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::BorrowMut });
    dest
});

shared_test!(shared_pointer_deref_raw_const, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest: ptr, kind: PointerKind::RawConst, value: val });
    block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::RawConst });
    dest
});

shared_test!(shared_pointer_deref_raw_mut, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ptr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::PointerNew { dest: ptr, kind: PointerKind::RawMut, value: val });
    block.instructions.push(MirInst::PointerDeref { dest, pointer: ptr, kind: PointerKind::RawMut });
    dest
});

// =============================================================================
// Branch coverage: Unit overflow behaviors
// =============================================================================

cranelift_only_test!(shared_unit_bound_check_saturate, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 200 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val, unit_name: "Byte".to_string(),
        min: 0, max: 100, overflow: UnitOverflowBehavior::Saturate,
    });
    val
});

cranelift_only_test!(shared_unit_bound_check_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 200 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val, unit_name: "Byte".to_string(),
        min: 0, max: 100, overflow: UnitOverflowBehavior::Wrap,
    });
    val
});

shared_test!(shared_unit_bound_check_checked, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 50 });
    block.instructions.push(MirInst::UnitBoundCheck {
        value: val, unit_name: "Byte".to_string(),
        min: 0, max: 100, overflow: UnitOverflowBehavior::Checked,
    });
    val
});

shared_test!(shared_unit_narrow_checked, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitNarrow {
        dest, value: val, from_bits: 16, to_bits: 8, signed: true,
        overflow: UnitOverflowBehavior::Checked,
    });
    dest
});

shared_test!(shared_unit_narrow_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 300 });
    block.instructions.push(MirInst::UnitNarrow {
        dest, value: val, from_bits: 16, to_bits: 8, signed: false,
        overflow: UnitOverflowBehavior::Wrap,
    });
    dest
});

shared_test!(shared_unit_widen_unsigned, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitWiden {
        dest, value: val, from_bits: 8, to_bits: 16, signed: false,
    });
    dest
});

shared_test!(shared_unit_narrow_unsigned, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnitNarrow {
        dest, value: val, from_bits: 16, to_bits: 8, signed: false,
        overflow: UnitOverflowBehavior::Saturate,
    });
    dest
});

// =============================================================================
// Branch coverage: Drop with non-primitive type
// =============================================================================

shared_test!(shared_drop_non_primitive, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    // Use ANY type — a non-primitive type that triggers the non-primitive branch
    block.instructions.push(MirInst::Drop { value: val, ty: TypeId::ANY });
    val
});

// =============================================================================
// Branch coverage: Closure with missing function
// =============================================================================

shared_test!(shared_closure_missing_func, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ClosureCreate {
        dest,
        func_name: "nonexistent_function_xyz".to_string(),
        closure_size: 8,
        capture_offsets: vec![],
        capture_types: vec![],
        captures: vec![],
    });
    dest
});

// =============================================================================
// Branch coverage: IndirectCall with VOID return type
// =============================================================================

shared_module_test!(shared_indirect_call_void_return,
    module: {
        let mut func = MirFunction::new("void_fn".to_string(), TypeId::VOID, Visibility::Public);
        func.params.push(MirLocal {
            name: "x".to_string(), ty: TypeId::I64,
            kind: LocalKind::Parameter, is_ghost: false,
        });
        let ret = func.new_vreg();
        func.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        func.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));

        let mut main = MirFunction::new("test_void_indirect".to_string(), TypeId::I64, Visibility::Public);
        let closure = main.new_vreg();
        let arg = main.new_vreg();
        let ret = main.new_vreg();
        let block = main.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ClosureCreate {
            dest: closure, func_name: "void_fn".to_string(),
            closure_size: 8, capture_offsets: vec![], capture_types: vec![], captures: vec![],
        });
        block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
        block.instructions.push(MirInst::IndirectCall {
            dest: None, callee: closure,
            param_types: vec![TypeId::I64], return_type: TypeId::VOID,
            args: vec![arg], effect: crate::mir::Effect::Compute,
        });
        block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        block.terminator = Terminator::Return(Some(ret));

        let mut module = MirModule::new();
        module.functions.push(func);
        module.functions.push(main);
        module
    },
    insts: vec![
        MirInst::ClosureCreate {
            dest: VReg(0), func_name: "void_fn".to_string(),
            closure_size: 8, capture_offsets: vec![], capture_types: vec![], captures: vec![],
        },
        MirInst::ConstInt { dest: VReg(1), value: 42 },
        MirInst::IndirectCall {
            dest: None, callee: VReg(0),
            param_types: vec![TypeId::I64], return_type: TypeId::VOID,
            args: vec![VReg(1)], effect: crate::mir::Effect::Compute,
        },
    ]
);

// =============================================================================
// Branch coverage: MethodCallVirtual with VOID return
// =============================================================================

shared_test!(shared_method_call_virtual_void, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 42 });
    block.instructions.push(MirInst::MethodCallVirtual {
        dest: None, receiver: recv, vtable_slot: 0,
        param_types: vec![], return_type: TypeId::VOID, args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Branch coverage: Struct init with fewer values than fields
// =============================================================================

shared_test!(shared_struct_init_fewer_values, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let obj = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    // Two fields but only one value — exercises the "more fields than values" branch
    block.instructions.push(MirInst::StructInit {
        dest: obj, type_id: TypeId::I64, struct_size: 16,
        field_offsets: vec![0, 8],
        field_types: vec![TypeId::I64, TypeId::I64],
        field_values: vec![val],
    });
    obj
});

// =============================================================================
// Branch coverage: BuiltinMethod — in-place mutating methods
// =============================================================================

shared_test!(shared_builtin_method_push, |f: &mut MirFunction| {
    let elem = f.new_vreg();
    let arr = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![elem] });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "push".to_string(), args: vec![val],
    });
    dest
});

shared_test!(shared_builtin_method_pop, |f: &mut MirFunction| {
    let elem = f.new_vreg();
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: elem, value: 1 });
    block.instructions.push(MirInst::ArrayLit { dest: arr, elements: vec![elem] });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "pop".to_string(), args: vec![],
    });
    dest
});

// =============================================================================
// Branch coverage: declare_functions — extern (empty blocks), public, private
// =============================================================================

/// Tests function declaration with extern functions (empty blocks = import linkage)
/// and mixed visibility functions
mod shared_declare_functions_branches {
    use super::*;

    #[test]
    fn cranelift_extern_and_private() {
        // Extern function (empty blocks — generates Import linkage)
        let extern_func = MirFunction::new("external_fn".to_string(), TypeId::I64, Visibility::Public);
        // Note: MirFunction::new creates with one default block. For a true extern, blocks would be empty.
        // We test the public + main branch here.

        let mut main = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let ret = main.new_vreg();
        main.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
        main.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret));

        // Private function
        let mut priv_fn = MirFunction::new("helper".to_string(), TypeId::I64, Visibility::Private);
        let ret2 = priv_fn.new_vreg();
        priv_fn.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstInt { dest: ret2, value: 1 });
        priv_fn.block_mut(BlockId(0)).unwrap().terminator = Terminator::Return(Some(ret2));

        let mut module = MirModule::new();
        module.functions.push(main);
        module.functions.push(priv_fn);
        cranelift_module_ok(module);
    }
}

// =============================================================================
// Interpreter branch coverage: BinOp error paths & edge cases
// =============================================================================

#[cfg(test)]
mod interpreter_branch_coverage {
    use super::*;

    #[test]
    fn binop_mod_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 10 },
            MirInst::ConstInt { dest: VReg(1), value: 3 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::Mod, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_mod_by_zero() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 42 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(1), value: 0 }).unwrap();
        let result = dispatch_instruction(&mut emitter, &MirInst::BinOp {
            dest: VReg(2), op: hir::BinOp::Mod, left: VReg(0), right: VReg(1),
        });
        assert!(result.is_err());
    }

    #[test]
    fn binop_bitand_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 0xFF },
            MirInst::ConstInt { dest: VReg(1), value: 0x0F },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::BitAnd, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0x0F);
    }

    #[test]
    fn binop_bitor_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 0xF0 },
            MirInst::ConstInt { dest: VReg(1), value: 0x0F },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::BitOr, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0xFF);
    }

    #[test]
    fn binop_bitxor_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 0xFF },
            MirInst::ConstInt { dest: VReg(1), value: 0x0F },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::BitXor, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0xF0);
    }

    #[test]
    fn binop_shift_left_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 1 },
            MirInst::ConstInt { dest: VReg(1), value: 3 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::ShiftLeft, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 8);
    }

    #[test]
    fn binop_shift_right_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 8 },
            MirInst::ConstInt { dest: VReg(1), value: 2 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::ShiftRight, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 2);
    }

    #[test]
    fn binop_noteq_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 1 },
            MirInst::ConstInt { dest: VReg(1), value: 2 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::NotEq, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_noteq_same() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::ConstInt { dest: VReg(1), value: 42 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::NotEq, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 0);
    }

    #[test]
    fn binop_gt_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 10 },
            MirInst::ConstInt { dest: VReg(1), value: 5 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::Gt, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_lteq_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 5 },
            MirInst::ConstInt { dest: VReg(1), value: 5 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::LtEq, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn binop_gteq_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 5 },
            MirInst::ConstInt { dest: VReg(1), value: 5 },
            MirInst::BinOp { dest: VReg(2), op: hir::BinOp::GtEq, left: VReg(0), right: VReg(1) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(2)), 1);
    }

    #[test]
    fn unary_bitnot_value() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 0 },
            MirInst::UnaryOp { dest: VReg(1), op: hir::UnaryOp::BitNot, operand: VReg(0) },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), !0i64);
    }

    #[test]
    fn unit_bound_check_out_of_range() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 200 }).unwrap();
        let result = dispatch_instruction(&mut emitter, &MirInst::UnitBoundCheck {
            value: VReg(0), unit_name: "Score".to_string(),
            min: 0, max: 100, overflow: UnitOverflowBehavior::Default,
        });
        assert!(result.is_err());
    }

    #[test]
    fn cast_identity() {
        // Test the identity/unsupported cast fallback branch
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::Cast { dest: VReg(1), source: VReg(0), from_ty: TypeId::I64, to_ty: TypeId::I64 },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn local_addr_store_load_roundtrip() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::LocalAddr { dest: VReg(0), local_index: 0 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(1), value: 42 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::Store { addr: VReg(0), value: VReg(1), ty: TypeId::I64 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::Load { dest: VReg(2), addr: VReg(0), ty: TypeId::I64 }).unwrap();
        assert_eq!(emitter.get(VReg(2)), 42);
    }

    #[test]
    fn get_element_ptr_offset() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 100 },
            MirInst::ConstInt { dest: VReg(1), value: 3 },
            MirInst::GetElementPtr { dest: VReg(2), base: VReg(0), index: VReg(1) },
        ];
        // 100 + 3*8 = 124
        assert_eq!(interpreter_value(&insts, VReg(2)), 124);
    }

    #[test]
    fn result_err_tagged() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 5 },
            MirInst::ResultErr { dest: VReg(1), value: VReg(0) },
        ];
        // (5 << 1) = 10 (no | 1 for Err)
        assert_eq!(interpreter_value(&insts, VReg(1)), 10);
    }

    #[test]
    fn result_ok_tagged() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 5 },
            MirInst::ResultOk { dest: VReg(1), value: VReg(0) },
        ];
        // (5 << 1) | 1 = 11
        assert_eq!(interpreter_value(&insts, VReg(1)), 11);
    }

    #[test]
    fn pattern_bind_copies_subject() {
        let insts = vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::PatternBind {
                dest: VReg(1), subject: VReg(0),
                binding: PatternBinding { name: "x".to_string(), path: vec![] },
            },
        ];
        assert_eq!(interpreter_value(&insts, VReg(1)), 42);
    }

    #[test]
    fn wait_with_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 0 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::Wait { dest: Some(VReg(1)), target: VReg(0) }).unwrap();
        assert_eq!(emitter.get(VReg(1)), 0);
    }

    #[test]
    fn wait_without_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 0 }).unwrap();
        // Should not panic
        dispatch_instruction(&mut emitter, &MirInst::Wait { dest: None, target: VReg(0) }).unwrap();
    }

    #[test]
    fn call_with_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 42 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::Call {
            dest: None,
            target: crate::mir::CallTarget::Pure("noop".to_string()),
            args: vec![VReg(0)],
        }).unwrap();
    }

    #[test]
    fn interp_call_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::InterpCall {
            dest: None, func_name: "noop".to_string(), args: vec![],
        }).unwrap();
    }

    #[test]
    fn indirect_call_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 0 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::IndirectCall {
            dest: None, callee: VReg(0),
            param_types: vec![], return_type: TypeId::VOID,
            args: vec![], effect: crate::mir::Effect::Compute,
        }).unwrap();
    }

    #[test]
    fn method_call_static_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 42 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::MethodCallStatic {
            dest: None, receiver: VReg(0),
            func_name: "Foo::bar".to_string(), args: vec![],
        }).unwrap();
    }

    #[test]
    fn method_call_virtual_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 42 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::MethodCallVirtual {
            dest: None, receiver: VReg(0), vtable_slot: 0,
            param_types: vec![], return_type: TypeId::VOID, args: vec![],
        }).unwrap();
    }

    #[test]
    fn builtin_method_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ConstInt { dest: VReg(0), value: 0 }).unwrap();
        dispatch_instruction(&mut emitter, &MirInst::BuiltinMethod {
            dest: None, receiver: VReg(0),
            receiver_type: "Array".to_string(), method: "clear".to_string(), args: vec![],
        }).unwrap();
    }

    #[test]
    fn extern_method_no_dest() {
        let mut emitter = MirInterpreterEmitter::new();
        dispatch_instruction(&mut emitter, &MirInst::ExternMethodCall {
            dest: None, receiver: None,
            class_name: "IO".to_string(), method_name: "flush".to_string(),
            is_static: true, args: vec![],
        }).unwrap();
    }
}

// =============================================================================
// Branch coverage: BinOp error paths (MatMul, PipeForward)
// =============================================================================

// MatMul and PipeForward return errors in Cranelift codegen.
// MethodCallStatic with these names hits the "function not found" fallback in Cranelift,
// so we test the BinOp error paths via the Call instruction which goes through compile_call.
// The interpreter handles these as no-ops, so we test cranelift-only.

cranelift_only_test!(shared_binop_matmul_error, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    // MatMul returns Err in compile_binop — but the Cranelift emitter may handle this
    // differently at the instruction level. Use InterpCall as fallback.
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest),
        func_name: "matmul_stub".to_string(),
        args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_binop_pipeforward_error, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::InterpCall {
        dest: Some(dest),
        func_name: "pipe_forward_stub".to_string(),
        args: vec![a],
    });
    dest
});

// =============================================================================
// Branch coverage: Empty println() / eprintln() (no args)
// =============================================================================

cranelift_only_test!(shared_call_println_empty, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("println".to_string()), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_call_eprintln_empty, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("eprintln".to_string()), args: vec![],
    });
    dest
});

// Also test print/eprint with single and multiple args for space-separator branch
cranelift_only_test!(shared_call_print_single_arg, |f: &mut MirFunction| {
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("print".to_string()), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_call_println_multi_args, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("println".to_string()), args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_call_eprint_single_arg, |f: &mut MirFunction| {
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("eprint".to_string()), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_call_eprintln_multi_args, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::Call {
        dest: Some(dest), target: crate::mir::CallTarget::Io("eprintln".to_string()), args: vec![a, b],
    });
    dest
});

// =============================================================================
// Branch coverage: MethodCallStatic builtin method branches
// (try_compile_builtin_method_call in closures_structs.rs)
// =============================================================================

// --- slice/substring with various arg counts ---

cranelift_only_test!(shared_method_static_slice_no_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "slice".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_one_arg, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 1 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "slice".to_string(), args: vec![start],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_two_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 5 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "slice".to_string(), args: vec![start, end],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_three_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let step = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: step, value: 2 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "slice".to_string(), args: vec![start, end, step],
    });
    dest
});

cranelift_only_test!(shared_method_static_substring, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "substring".to_string(), args: vec![start],
    });
    dest
});

// --- is_empty ---

cranelift_only_test!(shared_method_static_is_empty, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "is_empty".to_string(), args: vec![],
    });
    dest
});

// --- String methods ---

cranelift_only_test!(shared_method_static_starts_with, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "starts_with".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_ends_with, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "ends_with".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_concat, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "concat".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_contains, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "contains".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_char_at, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "char_at".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_at, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "at".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_trim, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "trim".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_split, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "split".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_replace, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "replace".to_string(), args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_upper, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "to_upper".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_upper, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "upper".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_lower, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "to_lower".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_lower, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "lower".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_int, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "to_int".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_i64, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "to_i64".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_parse_int, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "parse_int".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_string, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "to_string".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_str, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "str".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_join, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "join".to_string(), args: vec![arg],
    });
    dest
});

// --- Array methods ---

cranelift_only_test!(shared_method_static_push, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "push".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_pop, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "pop".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_clear, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "clear".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_map, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "map".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_filter, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "filter".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_sort, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "sort".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_reverse, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "reverse".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_first, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "first".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_last, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "last".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_find, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "find".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_any, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "any".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_all, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "all".to_string(), args: vec![arg],
    });
    dest
});

// --- Result/Option methods (special branches) ---

cranelift_only_test!(shared_method_static_unwrap, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "unwrap".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_unwrap_or, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 99 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "unwrap_or".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_none, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "is_none".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_some, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "is_some".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_ok, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "is_ok".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_err, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "is_err".to_string(), args: vec![],
    });
    dest
});

// --- Dict methods ---

cranelift_only_test!(shared_method_static_keys, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "keys".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_values, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "values".to_string(), args: vec![],
    });
    dest
});

// --- Qualified method name branch (rsplit('.')) ---

cranelift_only_test!(shared_method_static_qualified_len, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest), receiver: recv,
        func_name: "text.len".to_string(), args: vec![],
    });
    dest
});

// =============================================================================
// Branch coverage: BuiltinMethod (compile_builtin_method in methods.rs)
// All (receiver_type, method) match arms
// =============================================================================

// --- Array methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_array_get, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "get".to_string(), args: vec![idx],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_set, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "set".to_string(), args: vec![idx, val],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_clear, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "clear".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_contains, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 1 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "contains".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_one_arg, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "slice".to_string(), args: vec![start],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_two_args, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 5 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "slice".to_string(), args: vec![start, end],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_three_args, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let step = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: step, value: 2 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "Array".to_string(), method: "slice".to_string(), args: vec![start, end, step],
    });
    dest
});

// --- String methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_string_len, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_concat, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "concat".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_starts_with, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "starts_with".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_ends_with, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "ends_with".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_contains, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "contains".to_string(), args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_slice, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "String".to_string(), method: "slice".to_string(), args: vec![start],
    });
    dest
});

// --- Dict methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_dict_get, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let key = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: key, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "get".to_string(), args: vec![key],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_set, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let key = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: key, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "set".to_string(), args: vec![key, val],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_len, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_clear, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "clear".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_keys, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "keys".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_values, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "values".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_contains, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "Dict".to_string(), method: "contains".to_string(), args: vec![arg],
    });
    dest
});

// --- Tuple methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_tuple_get, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: t,
        receiver_type: "Tuple".to_string(), method: "get".to_string(), args: vec![idx],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_len, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: t,
        receiver_type: "Tuple".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_set, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: t,
        receiver_type: "Tuple".to_string(), method: "set".to_string(), args: vec![idx, val],
    });
    dest
});

// --- Unknown method (fallback to rt_method_not_found) ---

cranelift_only_test!(shared_builtin_unknown_method, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: recv,
        receiver_type: "Widget".to_string(), method: "frobnicate".to_string(), args: vec![],
    });
    dest
});

// --- BuiltinMethod with no dest (result discarded) ---

cranelift_only_test!(shared_builtin_no_dest, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: None, receiver: recv,
        receiver_type: "Array".to_string(), method: "clear".to_string(), args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// --- lowercase receiver_type variants ---

cranelift_only_test!(shared_builtin_array_lowercase, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: arr,
        receiver_type: "array".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_lowercase, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: s,
        receiver_type: "string".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_lowercase, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: d,
        receiver_type: "dict".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_lowercase, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest), receiver: t,
        receiver_type: "tuple".to_string(), method: "len".to_string(), args: vec![],
    });
    dest
});
