// Parallel iterator operation instruction compilation.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{ParallelBackend, VReg};

use super::{InstrContext, InstrResult};

/// Helper to convert ParallelBackend to runtime constant
fn backend_to_i32(backend: Option<ParallelBackend>) -> i32 {
    match backend {
        None => 0, // Auto-select
        Some(ParallelBackend::Cpu) => 1,
        Some(ParallelBackend::Simd) => 2,
        Some(ParallelBackend::Gpu) => 3,
    }
}

/// Get array length via runtime function call
fn get_array_length<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    array_val: cranelift_codegen::ir::Value,
) -> InstrResult<cranelift_codegen::ir::Value> {
    let func_id = ctx
        .runtime_funcs
        .get("rt_array_len")
        .ok_or_else(|| "rt_array_len not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    let call = builder.ins().call(func_ref, &[array_val]);
    Ok(builder.inst_results(call)[0])
}

/// Compile a parallel map operation
pub(crate) fn compile_par_map<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    input: VReg,
    closure: VReg,
    backend: Option<ParallelBackend>,
) -> InstrResult<()> {
    let input_val = ctx.vreg_values[&input];
    let closure_val = ctx.vreg_values[&closure];
    let backend_val = builder.ins().iconst(types::I32, backend_to_i32(backend) as i64);

    // Get the array length via runtime function
    let input_len = get_array_length(ctx, builder, input_val)?;

    let func_id = ctx
        .runtime_funcs
        .get("rt_par_map")
        .ok_or_else(|| "rt_par_map not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let call = builder
        .ins()
        .call(func_ref, &[input_val, input_len, closure_val, backend_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a parallel reduce operation
pub(crate) fn compile_par_reduce<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    input: VReg,
    initial: VReg,
    closure: VReg,
    backend: Option<ParallelBackend>,
) -> InstrResult<()> {
    let input_val = ctx.vreg_values[&input];
    let initial_val = ctx.vreg_values[&initial];
    let closure_val = ctx.vreg_values[&closure];
    let backend_val = builder.ins().iconst(types::I32, backend_to_i32(backend) as i64);

    // Get the array length via runtime function
    let input_len = get_array_length(ctx, builder, input_val)?;

    let func_id = ctx
        .runtime_funcs
        .get("rt_par_reduce")
        .ok_or_else(|| "rt_par_reduce not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let call = builder
        .ins()
        .call(func_ref, &[input_val, input_len, initial_val, closure_val, backend_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a parallel filter operation
pub(crate) fn compile_par_filter<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    input: VReg,
    predicate: VReg,
    backend: Option<ParallelBackend>,
) -> InstrResult<()> {
    let input_val = ctx.vreg_values[&input];
    let predicate_val = ctx.vreg_values[&predicate];
    let backend_val = builder.ins().iconst(types::I32, backend_to_i32(backend) as i64);

    // Get the array length via runtime function
    let input_len = get_array_length(ctx, builder, input_val)?;

    let func_id = ctx
        .runtime_funcs
        .get("rt_par_filter")
        .ok_or_else(|| "rt_par_filter not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let call = builder
        .ins()
        .call(func_ref, &[input_val, input_len, predicate_val, backend_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a parallel for_each operation
pub(crate) fn compile_par_for_each<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    input: VReg,
    closure: VReg,
    backend: Option<ParallelBackend>,
) -> InstrResult<()> {
    let input_val = ctx.vreg_values[&input];
    let closure_val = ctx.vreg_values[&closure];
    let backend_val = builder.ins().iconst(types::I32, backend_to_i32(backend) as i64);

    // Get the array length via runtime function
    let input_len = get_array_length(ctx, builder, input_val)?;

    let func_id = ctx
        .runtime_funcs
        .get("rt_par_for_each")
        .ok_or_else(|| "rt_par_for_each not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    builder
        .ins()
        .call(func_ref, &[input_val, input_len, closure_val, backend_val]);
    Ok(())
}
