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
    let val = match ctx.vreg_values.get(&src) {
        Some(&v) => v,
        None => return Err(format!("Copy: source vreg {:?} not found", src)),
    };
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
    let src_val = match ctx.vreg_values.get(&source) {
        Some(&v) => v,
        None => return Err(format!("Cast: source vreg {:?} not found", source)),
    };

    // Determine source and target types
    let is_from_float = from_ty == TypeId::F64 || from_ty == TypeId::F32;
    let is_to_float = to_ty == TypeId::F64 || to_ty == TypeId::F32;
    let to_int_width = match to_ty {
        TypeId::I8 | TypeId::U8 => Some(types::I8),
        TypeId::I16 | TypeId::U16 => Some(types::I16),
        TypeId::I32 | TypeId::U32 => Some(types::I32),
        TypeId::I64 | TypeId::U64 => Some(types::I64),
        _ => None,
    };
    let to_signed = matches!(to_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);
    let from_signed = matches!(from_ty, TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64);

    let val = if is_from_float && !is_to_float {
        // Float to int conversion
        let widened = if to_signed {
            builder.ins().fcvt_to_sint(types::I64, src_val)
        } else {
            builder.ins().fcvt_to_uint(types::I64, src_val)
        };
        match to_int_width {
            Some(types::I8) => builder.ins().ireduce(types::I8, widened),
            Some(types::I16) => builder.ins().ireduce(types::I16, widened),
            Some(types::I32) => builder.ins().ireduce(types::I32, widened),
            _ => widened,
        }
    } else if !is_from_float && is_to_float {
        // Int to float conversion
        if from_signed {
            builder.ins().fcvt_from_sint(types::F64, src_val)
        } else {
            builder.ins().fcvt_from_uint(types::F64, src_val)
        }
    } else if is_from_float && is_to_float {
        // Float to float (F32 <-> F64)
        if from_ty == TypeId::F32 {
            builder.ins().fpromote(types::F64, src_val)
        } else {
            builder.ins().fdemote(types::F32, src_val)
        }
    } else if let Some(target_ty) = to_int_width {
        let src_ty = builder.func.dfg.value_type(src_val);
        if src_ty == target_ty {
            src_val
        } else {
            match target_ty {
                types::I8 | types::I16 | types::I32 => builder.ins().ireduce(target_ty, src_val),
                types::I64 => match src_ty {
                    types::I8 | types::I16 | types::I32 => {
                        if from_signed {
                            builder.ins().sextend(types::I64, src_val)
                        } else {
                            builder.ins().uextend(types::I64, src_val)
                        }
                    }
                    _ => src_val,
                },
                _ => src_val,
            }
        }
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
    let val = match ctx.vreg_values.get(&operand) {
        Some(&v) => v,
        None => return Err(format!("UnaryOp: operand vreg {:?} not found", operand)),
    };
    let val_type = builder.func.dfg.value_type(val);
    let val_is_float = val_type == types::F32 || val_type == types::F64;
    let result = match op {
        UnaryOp::Neg => {
            if val_is_float {
                builder.ins().fneg(val)
            } else {
                builder.ins().ineg(val)
            }
        }
        UnaryOp::Not => {
            if val_is_float {
                let zero_f = if val_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().f64const(0.0)
                };
                builder
                    .ins()
                    .fcmp(cranelift_codegen::ir::condcodes::FloatCC::Equal, val, zero_f)
            } else {
                builder
                    .ins()
                    .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::Equal, val, 0)
            }
        }
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
    let source_val = match ctx.vreg_values.get(&source) {
        Some(&v) => v,
        None => return Err(format!("Spread: source vreg {:?} not found", source)),
    };
    ctx.vreg_values.insert(dest, source_val);
    Ok(())
}
