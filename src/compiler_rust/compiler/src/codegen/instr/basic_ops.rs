//! Basic operation instruction compilation.
//!
//! Handles simple operations: copy, cast, unary operations, and spread.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::{TypeId, UnaryOp};
use crate::mir::VReg;

use super::{InstrContext, InstrResult};

/// Compile Copy instruction: copies a value from one register to another
pub fn compile_copy<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    src: VReg,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&src];
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile Cast instruction: type conversion between numeric types
pub fn compile_cast<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    from_ty: TypeId,
    to_ty: TypeId,
) -> InstrResult<()> {
    let src_val = ctx.vreg_values[&source];

    // Determine source and target types
    let is_from_float = from_ty == TypeId::F64 || from_ty == TypeId::F32;
    let is_to_float = to_ty == TypeId::F64 || to_ty == TypeId::F32;
    let is_to_i64 = to_ty == TypeId::I64;

    let val = if is_from_float && !is_to_float {
        // Float to int conversion
        builder.ins().fcvt_to_sint(types::I64, src_val)
    } else if !is_from_float && is_to_float {
        // Int to float conversion
        builder.ins().fcvt_from_sint(types::F64, src_val)
    } else if is_from_float && is_to_float {
        // Float to float (F32 <-> F64)
        if from_ty == TypeId::F32 {
            builder.ins().fpromote(types::F64, src_val)
        } else {
            builder.ins().fdemote(types::F32, src_val)
        }
    } else if is_to_i64 {
        // Int to i64 (no-op or sign extension)
        src_val
    } else {
        // Default: just copy the value
        src_val
    };

    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile UnaryOp instruction: negation, logical not, bitwise not
pub fn compile_unary_op<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    op: UnaryOp,
    operand: VReg,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&operand];
    let result = match op {
        UnaryOp::Neg => builder.ins().ineg(val),
        UnaryOp::Not => builder
            .ins()
            .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::Equal, val, 0),
        UnaryOp::BitNot => builder.ins().bnot(val),
    };
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile Spread instruction: spreads a collection (currently just copies the value)
pub fn compile_spread<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];
    ctx.vreg_values.insert(dest, source_val);
    Ok(())
}
