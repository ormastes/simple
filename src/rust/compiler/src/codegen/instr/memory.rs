//! Memory instruction compilation
//!
//! This module handles compilation of memory-related instructions:
//! - LocalAddr - Get address of a local variable
//! - Load - Load a value from memory/local
//! - Store - Store a value to memory/local
//! - GetElementPtr - Calculate element address in an array
//! - GcAlloc - Allocate GC-managed memory
//! - Wait - Wait for an async operation

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::types_util::type_id_size;
use super::{InstrContext, InstrResult};

/// Compile LocalAddr instruction
pub fn compile_local_addr<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    local_index: usize,
) -> InstrResult<()> {
    let addr_val = builder.ins().iconst(types::I64, local_index as i64);
    ctx.vreg_values.insert(dest, addr_val);
    ctx.local_addr_map.insert(dest, local_index);
    Ok(())
}

/// Compile Load instruction
pub fn compile_load<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    addr: VReg,
) -> InstrResult<()> {
    if let Some(&local_index) = ctx.local_addr_map.get(&addr) {
        if let Some(&var) = ctx.variables.get(&local_index) {
            let val = builder.use_var(var);
            ctx.vreg_values.insert(dest, val);
        }
    } else {
        let val = ctx.vreg_values[&addr];
        ctx.vreg_values.insert(dest, val);
    }
    Ok(())
}

/// Compile Store instruction
pub fn compile_store<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    addr: VReg,
    value: VReg,
) -> InstrResult<()> {
    if let Some(&local_index) = ctx.local_addr_map.get(&addr) {
        if let Some(&var) = ctx.variables.get(&local_index) {
            // Get the expected type for this local
            let local_ty = if local_index < ctx.func.params.len() {
                ctx.func.params[local_index].ty
            } else {
                ctx.func.locals[local_index - ctx.func.params.len()].ty
            };
            let expected_cl_ty = super::super::types_util::type_id_to_cranelift(local_ty);

            // Helper to create default value of correct type
            let create_default = |builder: &mut FunctionBuilder| match expected_cl_ty {
                types::F32 => builder.ins().f32const(0.0),
                types::F64 => builder.ins().f64const(0.0),
                types::I8 => builder.ins().iconst(types::I8, 0),
                types::I16 => builder.ins().iconst(types::I16, 0),
                types::I32 => builder.ins().iconst(types::I32, 0),
                _ => builder.ins().iconst(types::I64, 0),
            };

            // Get the value, handling missing VRegs and type mismatches
            let val = if let Some(&v) = ctx.vreg_values.get(&value) {
                // Check type match - can mismatch in complex control flow
                let actual_ty = builder.func.dfg.value_type(v);
                if actual_ty != expected_cl_ty {
                    create_default(builder)
                } else {
                    v
                }
            } else {
                // Value not found - can happen when storing a value from an unvisited branch
                create_default(builder)
            };
            builder.def_var(var, val);
        }
    }
    Ok(())
}

/// Compile GetElementPtr instruction
pub fn compile_get_element_ptr<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    base: VReg,
    index: VReg,
) -> InstrResult<()> {
    let base_val = ctx.vreg_values[&base];
    let index_val = ctx.vreg_values[&index];
    let element_size = builder.ins().iconst(types::I64, 8);
    let offset = builder.ins().imul(index_val, element_size);
    let addr = builder.ins().iadd(base_val, offset);
    ctx.vreg_values.insert(dest, addr);
    Ok(())
}

/// Compile GcAlloc instruction
pub fn compile_gc_alloc<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    ty: TypeId,
) -> InstrResult<()> {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
    let size = type_id_size(ty) as i64;
    let size_val = builder.ins().iconst(types::I64, size.max(8));
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let ptr = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, ptr);
    Ok(())
}

/// Compile Wait instruction
pub fn compile_wait<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: Option<VReg>,
    target: VReg,
) -> InstrResult<()> {
    let wait_id = ctx.runtime_funcs["rt_wait"];
    let wait_ref = ctx.module.declare_func_in_func(wait_id, builder.func);
    let target_val = ctx.vreg_values[&target];
    let call = builder.ins().call(wait_ref, &[target_val]);
    let result = builder.inst_results(call)[0];
    if let Some(d) = dest {
        ctx.vreg_values.insert(d, result);
    }
    Ok(())
}
