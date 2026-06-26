//! Enum and Union instruction compilation
//!
//! This module handles compilation of enum and union type instructions:
//! - EnumDiscriminant - Get the discriminant of an enum
//! - EnumPayload - Extract payload from an enum variant
//! - UnionDiscriminant - Get the type index of a union
//! - UnionPayload - Extract payload from a union
//! - UnionWrap - Wrap a value into a union

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::{call_runtime_1, call_runtime_3};
use super::{InstrContext, InstrResult};

/// Compile EnumDiscriminant instruction
pub fn compile_enum_discriminant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) -> InstrResult<()> {
    let val = ctx.get_vreg(&value)?;
    let result = call_runtime_1(ctx, builder, "rt_enum_discriminant", val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile EnumPayload instruction
pub fn compile_enum_payload<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) -> InstrResult<()> {
    let val = ctx.get_vreg(&value)?;
    let result = call_runtime_1(ctx, builder, "rt_enum_payload", val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile UnionDiscriminant instruction
/// Unions use the same representation as enums
pub fn compile_union_discriminant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) -> InstrResult<()> {
    let val = ctx.get_vreg(&value)?;
    let result = call_runtime_1(ctx, builder, "rt_enum_discriminant", val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile UnionPayload instruction
/// Extract the payload value (type_index is for compile-time type safety)
pub fn compile_union_payload<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) -> InstrResult<()> {
    let val = ctx.get_vreg(&value)?;
    let result = call_runtime_1(ctx, builder, "rt_enum_payload", val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile UnionWrap instruction
/// Wrap a value into a union - use enum new with type index as discriminant
pub fn compile_union_wrap<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    type_index: u32,
) -> InstrResult<()> {
    let disc = builder.ins().iconst(types::I32, type_index as i64);
    // variant_count is not strictly needed for runtime, use 0
    let variant_count = builder.ins().iconst(types::I32, 0);
    let val = ctx.get_vreg(&value)?;
    let result = call_runtime_3(ctx, builder, "rt_enum_new", disc, variant_count, val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}
