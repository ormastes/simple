//! GPU instruction codegen for Cranelift.
//!
//! This module implements compilation of GPU MIR instructions to Cranelift IR.
//! GPU operations are implemented by calling runtime FFI functions.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{GpuAtomicOp, GpuMemoryScope, VReg};

use super::instr::{InstrContext, InstrResult};

/// Compile GpuGlobalId instruction
pub fn compile_gpu_global_id<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_global_id")
        .ok_or_else(|| "rt_gpu_global_id not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuLocalId instruction
pub fn compile_gpu_local_id<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_local_id")
        .ok_or_else(|| "rt_gpu_local_id not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuGroupId instruction
pub fn compile_gpu_group_id<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_group_id")
        .ok_or_else(|| "rt_gpu_group_id not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuGlobalSize instruction
pub fn compile_gpu_global_size<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_global_size")
        .ok_or_else(|| "rt_gpu_global_size not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuLocalSize instruction
pub fn compile_gpu_local_size<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_local_size")
        .ok_or_else(|| "rt_gpu_local_size not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuNumGroups instruction
pub fn compile_gpu_num_groups<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    dim: u8,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_num_groups")
        .ok_or_else(|| "rt_gpu_num_groups not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let dim_val = builder.ins().iconst(types::I32, dim as i64);
    let call = builder.ins().call(func_ref, &[dim_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuBarrier instruction
pub fn compile_gpu_barrier<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_barrier")
        .ok_or_else(|| "rt_gpu_barrier not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);
    builder.ins().call(func_ref, &[]);
    Ok(())
}

/// Compile GpuMemFence instruction
pub fn compile_gpu_mem_fence<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    scope: GpuMemoryScope,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_mem_fence")
        .ok_or_else(|| "rt_gpu_mem_fence not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let scope_val = match scope {
        GpuMemoryScope::WorkGroup => 0,
        GpuMemoryScope::Device => 1,
        GpuMemoryScope::All => 2,
    };
    let scope_arg = builder.ins().iconst(types::I32, scope_val);
    builder.ins().call(func_ref, &[scope_arg]);
    Ok(())
}

/// Compile GpuAtomic instruction
pub fn compile_gpu_atomic<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    op: GpuAtomicOp,
    ptr: VReg,
    value: VReg,
) -> InstrResult<()> {
    let ptr_val = ctx.vreg_values.get(&ptr)
        .ok_or_else(|| format!("ptr vreg {:?} not found", ptr))?;
    let value_val = ctx.vreg_values.get(&value)
        .ok_or_else(|| format!("value vreg {:?} not found", value))?;

    // Determine function name based on operation
    // Using i64 versions for now (could add type info to instruction for proper selection)
    let func_name = match op {
        GpuAtomicOp::Add => "rt_gpu_atomic_add_i64",
        GpuAtomicOp::Sub => "rt_gpu_atomic_sub_i64",
        GpuAtomicOp::Xchg => "rt_gpu_atomic_xchg_i64",
        GpuAtomicOp::Min => "rt_gpu_atomic_min_i64",
        GpuAtomicOp::Max => "rt_gpu_atomic_max_i64",
        GpuAtomicOp::And => "rt_gpu_atomic_and_i64",
        GpuAtomicOp::Or => "rt_gpu_atomic_or_i64",
        GpuAtomicOp::Xor => "rt_gpu_atomic_xor_i64",
    };

    let func_id = ctx.runtime_funcs.get(func_name)
        .ok_or_else(|| format!("{} not found", func_name))?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let call = builder.ins().call(func_ref, &[*ptr_val, *value_val]);
    let result = builder.inst_results(call)[0];

    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GpuSharedAlloc instruction
pub fn compile_gpu_shared_alloc<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    _element_type: crate::hir::TypeId,
    size: u32,
) -> InstrResult<()> {
    let func_id = ctx.runtime_funcs.get("rt_gpu_shared_alloc")
        .ok_or_else(|| "rt_gpu_shared_alloc not found".to_string())?;
    let func_ref = ctx.module.declare_func_in_func(*func_id, builder.func);

    let size_val = builder.ins().iconst(types::I64, size as i64);
    let call = builder.ins().call(func_ref, &[size_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}
