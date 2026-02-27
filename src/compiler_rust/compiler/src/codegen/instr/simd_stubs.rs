//! SIMD instruction compilation via runtime FFI delegation
//!
//! This module handles compilation of SIMD instructions by delegating
//! to runtime FFI functions. This provides correct functionality while
//! native Cranelift SIMD support can be added later for better performance.
//!
//! Instructions handled:
//! - VecLoad - Load SIMD vector from memory
//! - VecStore - Store SIMD vector to memory
//! - VecGather - Gather SIMD vector from scattered indices
//! - VecScatter - Scatter SIMD vector to scattered indices
//! - VecFma - Fused multiply-add
//! - VecRecip - Reciprocal
//! - VecMaskedLoad - Masked load
//! - VecMaskedStore - Masked store
//! - VecMinVec - Element-wise minimum
//! - VecMaxVec - Element-wise maximum
//! - VecClamp - Element-wise clamp
//! - NeighborLoad - Load from neighbor index

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::NeighborDirection;
use crate::mir::VReg;

use super::helpers::adapted_call;
use super::{InstrContext, InstrResult};

/// Compile NeighborLoad instruction via runtime FFI
pub fn compile_neighbor_load<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    array: VReg,
    direction: NeighborDirection,
) -> InstrResult<()> {
    let array_val = ctx.vreg_values[&array];
    // Convert direction to i64: 0 = Left (previous), 1 = Right (next)
    let dir_val = builder.ins().iconst(
        types::I64,
        match direction {
            NeighborDirection::Left => 0,
            NeighborDirection::Right => 1,
        },
    );

    let func_id = ctx
        .runtime_funcs
        .get("rt_neighbor_load")
        .ok_or_else(|| "rt_neighbor_load not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[array_val, dir_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecLoad instruction via runtime FFI
pub fn compile_vec_load<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    array: VReg,
    offset: VReg,
) -> InstrResult<()> {
    let array_val = ctx.vreg_values[&array];
    let offset_val = ctx.vreg_values[&offset];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_load")
        .ok_or_else(|| "rt_vec_load not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[array_val, offset_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecStore instruction via runtime FFI
pub fn compile_vec_store<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    source: VReg,
    array: VReg,
    offset: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];
    let array_val = ctx.vreg_values[&array];
    let offset_val = ctx.vreg_values[&offset];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_store")
        .ok_or_else(|| "rt_vec_store not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[source_val, array_val, offset_val]);
    Ok(())
}

/// Compile VecGather instruction via runtime FFI
pub fn compile_vec_gather<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    array: VReg,
    indices: VReg,
) -> InstrResult<()> {
    let array_val = ctx.vreg_values[&array];
    let indices_val = ctx.vreg_values[&indices];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_gather")
        .ok_or_else(|| "rt_vec_gather not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[array_val, indices_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecScatter instruction via runtime FFI
pub fn compile_vec_scatter<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    source: VReg,
    array: VReg,
    indices: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];
    let array_val = ctx.vreg_values[&array];
    let indices_val = ctx.vreg_values[&indices];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_scatter")
        .ok_or_else(|| "rt_vec_scatter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[source_val, array_val, indices_val]);
    Ok(())
}

/// Compile VecFma instruction via runtime FFI
pub fn compile_vec_fma<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    a: VReg,
    b: VReg,
    c: VReg,
) -> InstrResult<()> {
    let a_val = ctx.vreg_values[&a];
    let b_val = ctx.vreg_values[&b];
    let c_val = ctx.vreg_values[&c];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_fma")
        .ok_or_else(|| "rt_vec_fma not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[a_val, b_val, c_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecRecip instruction via runtime FFI
pub fn compile_vec_recip<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_recip")
        .ok_or_else(|| "rt_vec_recip not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[source_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecMaskedLoad instruction via runtime FFI
pub fn compile_vec_masked_load<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    array: VReg,
    offset: VReg,
    mask: VReg,
    default: VReg,
) -> InstrResult<()> {
    let array_val = ctx.vreg_values[&array];
    let offset_val = ctx.vreg_values[&offset];
    let mask_val = ctx.vreg_values[&mask];
    let default_val = ctx.vreg_values[&default];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_masked_load")
        .ok_or_else(|| "rt_vec_masked_load not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[array_val, offset_val, mask_val, default_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecMaskedStore instruction via runtime FFI
pub fn compile_vec_masked_store<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    source: VReg,
    array: VReg,
    offset: VReg,
    mask: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];
    let array_val = ctx.vreg_values[&array];
    let offset_val = ctx.vreg_values[&offset];
    let mask_val = ctx.vreg_values[&mask];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_masked_store")
        .ok_or_else(|| "rt_vec_masked_store not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    adapted_call(builder, func_ref, &[source_val, array_val, offset_val, mask_val]);
    Ok(())
}

/// Compile VecMinVec instruction via runtime FFI
pub fn compile_vec_min_vec<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    a: VReg,
    b: VReg,
) -> InstrResult<()> {
    let a_val = ctx.vreg_values[&a];
    let b_val = ctx.vreg_values[&b];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_min_vec")
        .ok_or_else(|| "rt_vec_min_vec not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[a_val, b_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecMaxVec instruction via runtime FFI
pub fn compile_vec_max_vec<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    a: VReg,
    b: VReg,
) -> InstrResult<()> {
    let a_val = ctx.vreg_values[&a];
    let b_val = ctx.vreg_values[&b];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_max_vec")
        .ok_or_else(|| "rt_vec_max_vec not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[a_val, b_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile VecClamp instruction via runtime FFI
pub fn compile_vec_clamp<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    lo: VReg,
    hi: VReg,
) -> InstrResult<()> {
    let source_val = ctx.vreg_values[&source];
    let lo_val = ctx.vreg_values[&lo];
    let hi_val = ctx.vreg_values[&hi];

    let func_id = ctx
        .runtime_funcs
        .get("rt_vec_clamp")
        .ok_or_else(|| "rt_vec_clamp not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[source_val, lo_val, hi_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}
