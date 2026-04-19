//! Scalar instruction tests: constants, basic ops, binop, cast.
//!
//! Covers: ConstInt/Float/Bool, Copy, UnaryOp, Cast, BinOp.

use super::{aot_compiles, aot_compiles_module};
use crate::hir::TypeId;
use crate::mir::{BlockId, MirFunction, MirInst, MirModule, Terminator, VReg};
use simple_parser::ast::Visibility;

// =============================================================================
// Constants (constants.rs)
// =============================================================================

#[test]
fn codegen_const_int() {
    assert!(aot_compiles("const_int", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest, value: 42 });
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
        block.instructions.push(MirInst::Cast {
            dest,
            source: fv,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
}

#[test]
fn codegen_const_bool_true() {
    assert!(aot_compiles("const_bool_t", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstBool { dest, value: true });
        dest
    }));
}

#[test]
fn codegen_const_bool_false() {
    assert!(aot_compiles("const_bool_f", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstBool { dest, value: false });
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
        block.instructions.push(MirInst::UnaryOp {
            dest,
            op: crate::hir::UnaryOp::Neg,
            operand: src,
        });
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
        block.instructions.push(MirInst::UnaryOp {
            dest,
            op: crate::hir::UnaryOp::Not,
            operand: src,
        });
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
    }));
}

// =============================================================================
// BinOp (core.rs)
// =============================================================================

#[test]
fn codegen_binop_all_ops() {
    let mut module = MirModule::new();

    fn make_binop_func(name: &str, op: crate::hir::BinOp, a: i64, b: i64) -> MirFunction {
        let mut f = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        let va = f.new_vreg();
        let vb = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: va, value: a });
        block.instructions.push(MirInst::ConstInt { dest: vb, value: b });
        block.instructions.push(MirInst::BinOp {
            dest,
            op,
            left: va,
            right: vb,
        });
        block.terminator = Terminator::Return(Some(dest));
        f
    }

    module
        .functions
        .push(make_binop_func("add_test", crate::hir::BinOp::Add, 10, 32));
    module
        .functions
        .push(make_binop_func("sub_test", crate::hir::BinOp::Sub, 50, 8));
    module
        .functions
        .push(make_binop_func("mul_test", crate::hir::BinOp::Mul, 6, 7));
    module
        .functions
        .push(make_binop_func("div_test", crate::hir::BinOp::Div, 84, 2));
    module
        .functions
        .push(make_binop_func("eq_test", crate::hir::BinOp::Eq, 42, 42));
    module.functions.push(make_binop_func("lt_test", crate::hir::BinOp::Lt, 5, 10));

    assert!(aot_compiles_module(module));
}
