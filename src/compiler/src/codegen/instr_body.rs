// Complete MIR function body compilation.
// This file is included by instr.rs.

/// Compile a complete MIR function body.
/// This is shared between AOT (cranelift.rs) and JIT (jit.rs) backends.
pub fn compile_function_body<M: Module>(
    module: &mut M,
    cranelift_func: &mut cranelift_codegen::ir::Function,
    func: &MirFunction,
    func_ids: &HashMap<String, cranelift_module::FuncId>,
    runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>,
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
        if let Some(entry_target) = func
            .block(func.entry_block)
            .and_then(|b| match b.terminator {
                Terminator::Jump(t) => Some(t),
                _ => None,
            })
        {
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
            let get_state_id = runtime_funcs.get("rt_async_get_state")
                .or_else(|| runtime_funcs.get("rt_future_get_state"))
                .copied();

            if let Some(get_state_id) = get_state_id {
                let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
                let call = builder.ins().call(get_state_ref, &[async_param]);
                let state_val = builder.inst_results(call)[0];

                let mut dispatch_blocks = Vec::new();
                if let Some(entry_target) = func
                    .block(func.entry_block)
                    .and_then(|b| match b.terminator {
                        Terminator::Jump(t) => Some(t),
                        _ => None,
                    })
                {
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
                }
            }
        }

        // Async resume block: restore live variables from future context
        if let Some(resume_map) = async_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let async_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs.get("rt_async_get_ctx")
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
                returned_via_yield = true;
                break;
            } else {
                let mut instr_ctx = InstrContext {
                    module,
                    func_ids,
                    runtime_funcs,
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
            }
        }

        // Compile terminator
        if returned_via_yield {
            continue;
        }
        if skip_entry_terminator && mir_block.id == func.entry_block {
            continue;
        }
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
                    let mut ret_val = vreg_values[v];
                    if generator_states.is_some() {
                        let wrap_id = runtime_funcs["rt_value_int"];
                        let wrap_ref = module.declare_func_in_func(wrap_id, builder.func);
                        let wrap_call = builder.ins().call(wrap_ref, &[ret_val]);
                        ret_val = builder.inst_results(wrap_call)[0];
                    }
                    builder.ins().return_(&[ret_val]);
                } else if generator_states.is_some() {
                    let nil_id = runtime_funcs["rt_value_nil"];
                    let nil_ref = module.declare_func_in_func(nil_id, builder.func);
                    let call = builder.ins().call(nil_ref, &[]);
                    let nil_val = builder.inst_results(call)[0];
                    builder.ins().return_(&[nil_val]);
                } else if func.return_type == TypeId::VOID {
                    builder.ins().return_(&[]);
                } else {
                    builder
                        .ins()
                        .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
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
                let cond_val = vreg_values[cond];
                let then_bl = *blocks.get(then_block).unwrap();
                let else_bl = *blocks.get(else_block).unwrap();
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Unreachable => {
                builder
                    .ins()
                    .trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
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
