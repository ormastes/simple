// Async, generator, and actor compilation for codegen.
// This file is included by instr.rs.

fn build_ctx_array<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    body_block: BlockId,
) -> cranelift_codegen::ir::Value {
    if let Some(meta) = ctx.func.outlined_bodies.get(&body_block) {
        if meta.live_ins.is_empty() {
            builder.ins().iconst(types::I64, 0)
        } else {
            let cap = builder.ins().iconst(types::I64, meta.live_ins.len() as i64);
            let new_id = ctx.runtime_funcs["rt_array_new"];
            let new_ref = ctx.module.declare_func_in_func(new_id, builder.func);
            let new_call = builder.ins().call(new_ref, &[cap]);
            let arr = builder.inst_results(new_call)[0];
            let push_id = ctx.runtime_funcs["rt_array_push"];
            let push_ref = ctx.module.declare_func_in_func(push_id, builder.func);
            for reg in &meta.live_ins {
                let val = ctx.vreg_values[reg];
                let _ = builder.ins().call(push_ref, &[arr, val]);
            }
            arr
        }
    } else {
        builder.ins().iconst(types::I64, 0)
    }
}

fn compile_future_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    body_block: BlockId,
) {
    let future_new_id = ctx.runtime_funcs["rt_future_new"];
    let future_new_ref = ctx.module.declare_func_in_func(future_new_id, builder.func);

    let body_ptr = get_func_block_addr(ctx.func_ids, ctx.module, &ctx.func.name, body_block, builder);
    let ctx_val = build_ctx_array(ctx, builder, body_block);
    let call = builder.ins().call(future_new_ref, &[body_ptr, ctx_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_actor_spawn<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    body_block: BlockId,
) {
    let spawn_id = ctx.runtime_funcs["rt_actor_spawn"];
    let spawn_ref = ctx.module.declare_func_in_func(spawn_id, builder.func);

    let body_ptr = get_func_block_addr(ctx.func_ids, ctx.module, &ctx.func.name, body_block, builder);
    let ctx_val = build_ctx_array(ctx, builder, body_block);
    let call = builder.ins().call(spawn_ref, &[body_ptr, ctx_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_generator_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    body_block: BlockId,
) {
    let gen_new_id = ctx.runtime_funcs["rt_generator_new"];
    let gen_new_ref = ctx.module.declare_func_in_func(gen_new_id, builder.func);

    let body_ptr = get_func_block_addr(ctx.func_ids, ctx.module, &ctx.func.name, body_block, builder);
    let ctx_val = build_ctx_array(ctx, builder, body_block);
    let slot_count = ctx.func.outlined_bodies.get(&body_block)
        .map(|meta| meta.frame_slots.unwrap_or(0) as i64)
        .unwrap_or(0);
    let slots_val = builder.ins().iconst(types::I64, slot_count);
    let call = builder.ins().call(gen_new_ref, &[body_ptr, slots_val, ctx_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_yield<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    value: VReg,
) -> InstrResult<()> {
    if let Some(state_map) = ctx.generator_state_map.as_ref() {
        if let Some(state) = state_map.get(&ctx.mir_block_id) {
            let gen_param = builder.block_params(ctx.entry_block)[0];
            let store_id = ctx.runtime_funcs["rt_generator_store_slot"];
            let store_ref = ctx.module.declare_func_in_func(store_id, builder.func);
            for (idx, reg) in state.live_after_yield.iter().enumerate() {
                let val = ctx.vreg_values[reg];
                let idx_val = builder.ins().iconst(types::I64, idx as i64);
                let _ = builder.ins().call(store_ref, &[gen_param, idx_val, val]);
            }

            let set_state_id = ctx.runtime_funcs["rt_generator_set_state"];
            let set_state_ref = ctx.module.declare_func_in_func(set_state_id, builder.func);
            let next_state = builder.ins().iconst(types::I64, (state.state_id + 1) as i64);
            let _ = builder.ins().call(set_state_ref, &[gen_param, next_state]);

            let val = ctx.vreg_values[&value];
            builder.ins().return_(&[val]);
            return Ok(());
        }
    }
    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(2));
    Ok(())
}
