// Complete MIR function body compilation.

use cranelift_codegen::ir::{condcodes::IntCC, types, InstBuilder};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;
use std::collections::{HashMap, HashSet};

use crate::hir::TypeId;
use crate::mir::{BlockId, MirFunction, MirInst, Terminator, VReg};

use super::super::types_util::type_to_cranelift;
use super::async_ops::compile_yield;
use super::{compile_instruction, InstrContext, InstrResult};

/// Collect all VRegs used as destinations in a MIR function.
fn collect_all_dest_vregs(func: &MirFunction) -> HashSet<VReg> {
    let mut vregs = HashSet::new();
    for block in &func.blocks {
        for inst in &block.instructions {
            if let Some(dest) = inst.dest() {
                vregs.insert(dest);
            }
        }
        // Also collect VRegs used in terminators (branch conditions, return values)
        match &block.terminator {
            Terminator::Return(Some(v)) => { vregs.insert(*v); }
            Terminator::Branch { cond, .. } => { vregs.insert(*cond); }
            _ => {}
        }
    }
    vregs
}

/// Coerce a value to i64 for storage in a Variable declared as i64.
fn coerce_to_i64(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let ty = builder.func.dfg.value_type(val);
    if ty == types::I64 {
        val
    } else if ty.is_int() && ty.bits() < 64 {
        builder.ins().sextend(types::I64, val)
    } else if ty.is_int() && ty.bits() > 64 {
        builder.ins().ireduce(types::I64, val)
    } else if ty.is_float() {
        builder.ins().bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val)
    } else {
        // For vector types etc., just use as-is (will be i64 in most cases)
        val
    }
}

/// Safely def_var with type coercion to i64.
fn def_var_coerced(
    builder: &mut FunctionBuilder,
    var: Variable,
    val: cranelift_codegen::ir::Value,
) {
    let coerced = coerce_to_i64(builder, val);
    builder.def_var(var, coerced);
}

/// Sync vreg_values → Variables: call def_var for all vregs that have values.
fn sync_vregs_to_vars(
    builder: &mut FunctionBuilder,
    vreg_values: &HashMap<VReg, cranelift_codegen::ir::Value>,
    vreg_vars: &HashMap<VReg, Variable>,
) {
    for (vreg, &val) in vreg_values {
        if let Some(&var) = vreg_vars.get(vreg) {
            def_var_coerced(builder, var, val);
        }
    }
}

/// Sync Variables → vreg_values: call use_var for all declared vreg Variables.
fn sync_vars_to_vregs(
    builder: &mut FunctionBuilder,
    vreg_values: &mut HashMap<VReg, cranelift_codegen::ir::Value>,
    vreg_vars: &HashMap<VReg, Variable>,
) {
    for (&vreg, &var) in vreg_vars {
        let val = builder.use_var(var);
        vreg_values.insert(vreg, val);
    }
}

/// Compile a complete MIR function body.
/// This is shared between AOT (cranelift.rs) and JIT (jit.rs) backends.
pub fn compile_function_body<M: Module>(
    module: &mut M,
    cranelift_func: &mut cranelift_codegen::ir::Function,
    func: &MirFunction,
    func_ids: &HashMap<String, cranelift_module::FuncId>,
    runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>,
    global_ids: &HashMap<String, cranelift_module::DataId>,
) -> InstrResult<()> {
    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(cranelift_func, &mut func_ctx);

    // Create variables for parameters and locals
    let mut variables = HashMap::new();
    let mut var_idx = 0u32;

    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(param.ty);
        builder.declare_var(var, ty);
        variables.insert(i, var);
        var_idx += 1;
    }

    for (i, local) in func.locals.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(local.ty);
        builder.declare_var(var, ty);
        variables.insert(func.params.len() + i, var);
        var_idx += 1;
    }

    // Track values and blocks
    let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();

    // Declare Cranelift Variables for all VRegs to handle SSA across blocks.
    // This lets Cranelift automatically insert phi nodes (block params) where needed.
    let mut vreg_vars: HashMap<VReg, Variable> = HashMap::new();
    {
        let all_vregs = collect_all_dest_vregs(func);
        for vreg in &all_vregs {
            let var = Variable::from_u32(var_idx);
            builder.declare_var(var, types::I64); // default to i64; type is refined on def_var
            vreg_vars.insert(*vreg, var);
            var_idx += 1;
        }
    }

    // Create blocks
    let mut blocks = HashMap::new();
    for mir_block in &func.blocks {
        let cl_block = builder.create_block();
        blocks.insert(mir_block.id, cl_block);
    }

    // Entry block gets parameters
    let entry_block = *blocks.get(&func.entry_block).unwrap();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Initialize parameter variables
    for (i, _param) in func.params.iter().enumerate() {
        let val = builder.block_params(entry_block)[i];
        let var = variables[&i];
        builder.def_var(var, val);
    }

    // If this is an outlined body with captures, load them from ctx (last param).
    if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
        if !meta.live_ins.is_empty() {
            let ctx_param = if func.generator_states.is_some() {
                let gen_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs["rt_generator_get_ctx"];
                let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                let call = builder.ins().call(get_ctx_ref, &[gen_param]);
                builder.inst_results(call)[0]
            } else {
                builder.block_params(entry_block)[func.params.len().saturating_sub(1)]
            };
            let get_id = runtime_funcs["rt_array_get"];
            let get_ref = module.declare_func_in_func(get_id, builder.func);
            for (idx, reg) in meta.live_ins.iter().enumerate() {
                let idx_val = builder.ins().iconst(types::I64, idx as i64);
                let call = builder.ins().call(get_ref, &[ctx_param, idx_val]);
                let val = builder.inst_results(call)[0];
                vreg_values.insert(*reg, val);
                if let Some(&var) = vreg_vars.get(reg) {
                    def_var_coerced(&mut builder, var, val);
                }
            }
        }
    }

    let generator_states = func.generator_states.clone();
    let generator_state_len = generator_states.as_ref().map(|s| s.len()).unwrap_or(0);
    let generator_done_state = generator_state_len + 1;
    let generator_state_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.yield_block, s.clone());
        }
        map
    });
    let generator_resume_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.resume_block, s.clone());
        }
        map
    });

    // Async state machine dispatcher (similar to generator but for futures)
    let async_states = func.async_states.clone();
    let async_state_len = async_states.as_ref().map(|s| s.len()).unwrap_or(0);
    let async_done_state = async_state_len + 1;
    let async_state_map = async_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.await_block, s.clone());
        }
        map
    });
    let async_resume_map = async_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.resume_block, s.clone());
        }
        map
    });

    let mut skip_entry_terminator = false;
    if let Some(states) = &generator_states {
        let generator_param = builder.block_params(entry_block)[0];
        let get_state_id = runtime_funcs["rt_generator_get_state"];
        let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
        let call = builder.ins().call(get_state_ref, &[generator_param]);
        let state_val = builder.inst_results(call)[0];

        let mut dispatch_blocks = Vec::new();
        if let Some(entry_target) = func.block(func.entry_block).and_then(|b| match b.terminator {
            Terminator::Jump(t) => Some(t),
            _ => None,
        }) {
            let target_block = *blocks.get(&entry_target).unwrap();
            let mut targets = Vec::new();
            targets.push(target_block);
            for st in states {
                targets.push(*blocks.get(&st.resume_block).unwrap());
            }
            let default_block = func
                .generator_complete
                .and_then(|b| blocks.get(&b).copied())
                .unwrap_or(target_block);
            targets.push(default_block); // done state

            let mut current_block = entry_block;
            let mut is_first = true;
            for (idx, tgt) in targets.iter().enumerate() {
                if !is_first {
                    builder.switch_to_block(current_block);
                } else {
                    is_first = false;
                }
                let is_last = idx == targets.len() - 1;
                let next_block = if is_last {
                    default_block
                } else {
                    let nb = builder.create_block();
                    dispatch_blocks.push(nb);
                    nb
                };
                let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
                builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
                if !is_last {
                    current_block = next_block;
                }
            }
            builder.switch_to_block(default_block);
            skip_entry_terminator = true;

            for b in dispatch_blocks {
                builder.seal_block(b);
            }
        }
    }

    // Async state machine dispatcher (for async functions with multiple await points)
    if let Some(states) = &async_states {
        if !skip_entry_terminator {
            let async_param = builder.block_params(entry_block)[0];
            let get_state_id = runtime_funcs
                .get("rt_async_get_state")
                .or_else(|| runtime_funcs.get("rt_future_get_state"))
                .copied();

            if let Some(get_state_id) = get_state_id {
                let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
                let call = builder.ins().call(get_state_ref, &[async_param]);
                let state_val = builder.inst_results(call)[0];

                let mut dispatch_blocks = Vec::new();
                if let Some(entry_target) = func.block(func.entry_block).and_then(|b| match b.terminator {
                    Terminator::Jump(t) => Some(t),
                    _ => None,
                }) {
                    let target_block = *blocks.get(&entry_target).unwrap();
                    let mut targets = Vec::new();
                    targets.push(target_block); // State 0: initial entry
                    for st in states {
                        targets.push(*blocks.get(&st.resume_block).unwrap());
                    }
                    let default_block = func
                        .async_complete
                        .and_then(|b| blocks.get(&b).copied())
                        .unwrap_or(target_block);
                    targets.push(default_block); // Done state

                    let mut current_block = entry_block;
                    let mut is_first = true;
                    for (idx, tgt) in targets.iter().enumerate() {
                        if !is_first {
                            builder.switch_to_block(current_block);
                        } else {
                            is_first = false;
                        }
                        let is_last = idx == targets.len() - 1;
                        let next_block = if is_last {
                            default_block
                        } else {
                            let nb = builder.create_block();
                            dispatch_blocks.push(nb);
                            nb
                        };
                        let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
                        builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
                        if !is_last {
                            current_block = next_block;
                        }
                    }
                    builder.switch_to_block(default_block);
                    skip_entry_terminator = true;

                    for b in dispatch_blocks {
                        builder.seal_block(b);
                    }
                }
            }
        }
    }

    // Compile each block
    let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();

    for mir_block in &func.blocks {
        if generator_states.is_some() && mir_block.id == func.entry_block {
            continue;
        }
        if async_states.is_some() && mir_block.id == func.entry_block {
            continue;
        }
        let cl_block = *blocks.get(&mir_block.id).unwrap();

        if mir_block.id != func.entry_block {
            builder.switch_to_block(cl_block);
            // At block entry, populate vreg_values from Variables (SSA phi resolution)
            sync_vars_to_vregs(&mut builder, &mut vreg_values, &vreg_vars);
        }

        if let Some(resume_map) = generator_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let gen_param = builder.block_params(entry_block)[0];
                let load_id = runtime_funcs["rt_generator_load_slot"];
                let load_ref = module.declare_func_in_func(load_id, builder.func);
                for (idx, reg) in state.live_after_yield.iter().enumerate() {
                    let idx_val = builder.ins().iconst(types::I64, idx as i64);
                    let call = builder.ins().call(load_ref, &[gen_param, idx_val]);
                    let val = builder.inst_results(call)[0];
                    vreg_values.insert(*reg, val);
                    if let Some(&var) = vreg_vars.get(reg) {
                        builder.def_var(var, val);
                    }
                }
            }
        }

        // Async resume block: restore live variables from future context
        if let Some(resume_map) = async_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let async_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs
                    .get("rt_async_get_ctx")
                    .or_else(|| runtime_funcs.get("rt_future_get_ctx"))
                    .copied();
                if let Some(get_ctx_id) = get_ctx_id {
                    let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                    let call = builder.ins().call(get_ctx_ref, &[async_param]);
                    let ctx_val = builder.inst_results(call)[0];

                    let get_id = runtime_funcs["rt_array_get"];
                    let get_ref = module.declare_func_in_func(get_id, builder.func);
                    for (idx, reg) in state.live_after_await.iter().enumerate() {
                        let idx_val = builder.ins().iconst(types::I64, idx as i64);
                        let call = builder.ins().call(get_ref, &[ctx_val, idx_val]);
                        let val = builder.inst_results(call)[0];
                        vreg_values.insert(*reg, val);
                        if let Some(&var) = vreg_vars.get(reg) {
                            builder.def_var(var, val);
                        }
                    }
                }
            }
        }

        // Compile instructions; if we hit a Yield, it already emits a return, so skip the terminator.
        let mut returned_via_yield = false;
        for inst in &mir_block.instructions {
            if let MirInst::Yield { value } = inst {
                let mut instr_ctx = InstrContext {
                    module,
                    func_ids,
                    runtime_funcs,
                    global_ids,
                    vreg_values: &mut vreg_values,
                    local_addr_map: &mut local_addr_map,
                    variables: &variables,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                };
                compile_yield(&mut instr_ctx, &mut builder, *value)?;
                // Sync vreg_values → Variables after yield
                sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars);
                returned_via_yield = true;
                break;
            } else {
                let mut instr_ctx = InstrContext {
                    module,
                    func_ids,
                    runtime_funcs,
                    global_ids,
                    vreg_values: &mut vreg_values,
                    local_addr_map: &mut local_addr_map,
                    variables: &variables,
                    func,
                    entry_block,
                    blocks: &blocks,
                    mir_block_id: mir_block.id,
                    generator_state_map: &generator_state_map,
                    async_state_map: &async_state_map,
                };
                compile_instruction(&mut instr_ctx, &mut builder, inst)?;
                // Ensure all vreg values are i64 (extend smaller int types)
                // and sync to Variables for cross-block SSA
                if let Some(dest) = inst.dest() {
                    if let Some(&val) = vreg_values.get(&dest) {
                        let ty = builder.func.dfg.value_type(val);
                        if ty.is_int() && ty.bits() < 64 {
                            let extended = builder.ins().sextend(types::I64, val);
                            vreg_values.insert(dest, extended);
                            if let Some(&var) = vreg_vars.get(&dest) {
                                builder.def_var(var, extended);
                            }
                        } else if let Some(&var) = vreg_vars.get(&dest) {
                            def_var_coerced(&mut builder, var, val);
                        }
                    }
                }
            }
        }

        // Compile terminator
        if returned_via_yield {
            continue;
        }
        if skip_entry_terminator && mir_block.id == func.entry_block {
            continue;
        }
        // Sync all vreg_values to Variables before terminators (for cross-block SSA)
        sync_vregs_to_vars(&mut builder, &vreg_values, &vreg_vars);
        match &mir_block.terminator {
            Terminator::Return(val) => {
                let mut mark_done = false;
                let mut next_state_val = generator_done_state as i64;
                if let Some(map) = generator_state_map.as_ref() {
                    if let Some(state) = map.get(&mir_block.id) {
                        next_state_val = (state.state_id + 1) as i64;
                    } else {
                        mark_done = true;
                    }
                }
                if generator_states.is_some() {
                    let gen_param = builder.block_params(entry_block)[0];
                    let set_state_id = runtime_funcs["rt_generator_set_state"];
                    let set_state_ref = module.declare_func_in_func(set_state_id, builder.func);
                    let next_state = builder.ins().iconst(types::I64, next_state_val);
                    let _ = builder.ins().call(set_state_ref, &[gen_param, next_state]);
                    if mark_done || next_state_val == generator_done_state as i64 {
                        let mark_id = runtime_funcs["rt_generator_mark_done"];
                        let mark_ref = module.declare_func_in_func(mark_id, builder.func);
                        let _ = builder.ins().call(mark_ref, &[gen_param]);
                    }
                }
                if let Some(v) = val {
                    // If function returns void, discard the return value
                    // (this can happen when return with value is used in a void function)
                    if func.return_type == TypeId::VOID {
                        builder.ins().return_(&[]);
                    } else {
                        let ret_ty = type_to_cranelift(func.return_type);
                        // Handle missing VReg (can happen in complex control flow)
                        let mut ret_val = if let Some(&rv) = vreg_values.get(v) {
                            // Coerce value type to match function return type
                            let val_type = builder.func.dfg.value_type(rv);
                            if val_type == ret_ty {
                                rv
                            } else if val_type == types::I64
                                && (ret_ty == types::I32 || ret_ty == types::I16 || ret_ty == types::I8)
                            {
                                // Truncate i64 to smaller integer type
                                builder.ins().ireduce(ret_ty, rv)
                            } else if (val_type == types::I8 || val_type == types::I16 || val_type == types::I32)
                                && ret_ty == types::I64
                            {
                                // Extend smaller integer to i64
                                builder.ins().sextend(types::I64, rv)
                            } else {
                                rv
                            }
                        } else {
                            // Return a default value of the correct type
                            match ret_ty {
                                types::F32 => builder.ins().f32const(0.0),
                                types::F64 => builder.ins().f64const(0.0),
                                types::I8 => builder.ins().iconst(types::I8, 0),
                                types::I16 => builder.ins().iconst(types::I16, 0),
                                types::I32 => builder.ins().iconst(types::I32, 0),
                                _ => builder.ins().iconst(types::I64, 0),
                            }
                        };
                        if generator_states.is_some() {
                            let wrap_id = runtime_funcs["rt_value_int"];
                            let wrap_ref = module.declare_func_in_func(wrap_id, builder.func);
                            let wrap_call = builder.ins().call(wrap_ref, &[ret_val]);
                            ret_val = builder.inst_results(wrap_call)[0];
                        }
                        builder.ins().return_(&[ret_val]);
                    }
                } else if generator_states.is_some() {
                    let nil_id = runtime_funcs["rt_value_nil"];
                    let nil_ref = module.declare_func_in_func(nil_id, builder.func);
                    let call = builder.ins().call(nil_ref, &[]);
                    let nil_val = builder.inst_results(call)[0];
                    builder.ins().return_(&[nil_val]);
                } else if func.return_type == TypeId::VOID {
                    builder.ins().return_(&[]);
                } else {
                    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
            }

            Terminator::Jump(target) => {
                let target_block = *blocks.get(target).unwrap();
                builder.ins().jump(target_block, &[]);
            }

            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond_val = vreg_values.get(cond).copied().unwrap_or_else(|| {
                    // Use Variable if available, otherwise default to 0
                    if let Some(&var) = vreg_vars.get(cond) {
                        builder.use_var(var)
                    } else {
                        builder.ins().iconst(types::I64, 0)
                    }
                });
                // brif expects i8 (boolean), coerce if needed
                let cond_ty = builder.func.dfg.value_type(cond_val);
                let cond_val = if cond_ty != types::I8 && cond_ty.is_int() {
                    builder.ins().icmp_imm(IntCC::NotEqual, cond_val, 0)
                } else {
                    cond_val
                };
                let then_bl = *blocks.get(then_block).unwrap();
                let else_bl = *blocks.get(else_block).unwrap();
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            }
        }
    }

    // Seal all blocks after all predecessors are known
    for mir_block in &func.blocks {
        let cl_block = *blocks.get(&mir_block.id).unwrap();
        builder.seal_block(cl_block);
    }

    builder.finalize();
    Ok(())
}
