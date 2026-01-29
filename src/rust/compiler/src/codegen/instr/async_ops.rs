// Async, generator, and actor compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;
use std::collections::HashMap;

use crate::mir::{BlockId, VReg};

use super::super::shared::get_func_block_addr;
use super::{InstrContext, InstrResult};

pub(crate) fn build_ctx_array<M: Module>(
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

pub(crate) fn compile_future_create<M: Module>(
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

pub(crate) fn compile_actor_spawn<M: Module>(
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

pub(crate) fn compile_generator_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    body_block: BlockId,
) {
    let gen_new_id = ctx.runtime_funcs["rt_generator_new"];
    let gen_new_ref = ctx.module.declare_func_in_func(gen_new_id, builder.func);

    let body_ptr = get_func_block_addr(ctx.func_ids, ctx.module, &ctx.func.name, body_block, builder);
    let ctx_val = build_ctx_array(ctx, builder, body_block);
    let slot_count = ctx
        .func
        .outlined_bodies
        .get(&body_block)
        .map(|meta| meta.frame_slots.unwrap_or(0) as i64)
        .unwrap_or(0);
    let slots_val = builder.ins().iconst(types::I64, slot_count);
    let call = builder.ins().call(gen_new_ref, &[body_ptr, slots_val, ctx_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

pub(crate) fn compile_yield<M: Module>(
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
            // Wrap the yielded value as a RuntimeValue so the dispatcher ABI
            // matches the runtime's expectations.
            let wrap_id = ctx.runtime_funcs["rt_value_int"];
            let wrap_ref = ctx.module.declare_func_in_func(wrap_id, builder.func);
            let wrap_call = builder.ins().call(wrap_ref, &[val]);
            let wrapped = builder.inst_results(wrap_call)[0];
            builder.ins().return_(&[wrapped]);
            return Ok(());
        }
    }
    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(2));
    Ok(())
}

/// Compile an Await instruction with state machine support.
/// Similar to Yield but for async functions: saves state, returns suspended future.
pub(crate) fn compile_await<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    future: VReg,
    mir_block_id: BlockId,
    entry_block: cranelift_codegen::ir::Block,
) -> InstrResult<()> {
    // Check if we have async state map for this block
    if let Some(async_state_map) = ctx.async_state_map.as_ref() {
        if let Some(state) = async_state_map.get(&mir_block_id) {
            let async_param = builder.block_params(entry_block)[0];

            // Save live variables to async context
            let get_ctx_id = ctx
                .runtime_funcs
                .get("rt_async_get_ctx")
                .or_else(|| ctx.runtime_funcs.get("rt_future_get_ctx"))
                .copied();
            if let Some(get_ctx_id) = get_ctx_id {
                let get_ctx_ref = ctx.module.declare_func_in_func(get_ctx_id, builder.func);
                let call = builder.ins().call(get_ctx_ref, &[async_param]);
                let ctx_val = builder.inst_results(call)[0];

                let push_id = ctx.runtime_funcs["rt_array_push"];
                let push_ref = ctx.module.declare_func_in_func(push_id, builder.func);
                for reg in &state.live_after_await {
                    if let Some(val) = ctx.vreg_values.get(reg) {
                        let _ = builder.ins().call(push_ref, &[ctx_val, *val]);
                    }
                }
            }

            // Set next state (resume at next block)
            let set_state_id = ctx
                .runtime_funcs
                .get("rt_async_set_state")
                .or_else(|| ctx.runtime_funcs.get("rt_future_set_state"))
                .copied();
            if let Some(set_state_id) = set_state_id {
                let set_state_ref = ctx.module.declare_func_in_func(set_state_id, builder.func);
                let next_state = builder.ins().iconst(types::I64, (state.state_id + 1) as i64);
                let _ = builder.ins().call(set_state_ref, &[async_param, next_state]);
            }

            // Return the future itself (suspended state)
            // Wrap as RuntimeValue for ABI compatibility
            let future_val = ctx.vreg_values[&future];
            let wrap_id = ctx
                .runtime_funcs
                .get("rt_value_future")
                .or_else(|| ctx.runtime_funcs.get("rt_value_int")) // Fallback
                .copied();
            if let Some(wrap_id) = wrap_id {
                let wrap_ref = ctx.module.declare_func_in_func(wrap_id, builder.func);
                let wrap_call = builder.ins().call(wrap_ref, &[future_val]);
                let wrapped = builder.inst_results(wrap_call)[0];
                builder.ins().return_(&[wrapped]);
            } else {
                builder.ins().return_(&[future_val]);
            }
            return Ok(());
        }
    }

    // Fallback: no state machine — use cooperative scheduler if available,
    // otherwise fall back to eager (blocking) await.
    let await_id = ctx
        .runtime_funcs
        .get("rt_async_schedule_await")
        .or_else(|| ctx.runtime_funcs.get("rt_future_await"))
        .or_else(|| ctx.runtime_funcs.get("rt_await"))
        .copied();
    if let Some(await_id) = await_id {
        let await_ref = ctx.module.declare_func_in_func(await_id, builder.func);
        let future_val = ctx.vreg_values[&future];
        let call = builder.ins().call(await_ref, &[future_val]);
        let result = builder.inst_results(call)[0];
        ctx.vreg_values.insert(dest, result);
    } else {
        builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(3));
    }
    Ok(())
}

// ============================================================================
// Monoio Direct Await (Feature: monoio-direct)
// ============================================================================

/// Compile an await for MonoioFuture with direct polling.
///
/// This generates code that:
/// 1. Polls the MonoioFuture using rt_monoio_poll
/// 2. Checks if result is PENDING_MARKER (-1)
/// 3. If pending, saves state and returns suspended
/// 4. If ready, extracts result and continues
///
/// # Arguments
/// * `ctx` - Instruction context
/// * `builder` - Function builder
/// * `dest` - Destination register for result
/// * `future` - Register containing MonoioFuture
/// * `mir_block_id` - Current MIR block ID
/// * `entry_block` - Entry block for state machine
#[allow(dead_code)]
pub(crate) fn compile_await_monoio<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    future: VReg,
    mir_block_id: BlockId,
    entry_block: cranelift_codegen::ir::Block,
) -> InstrResult<()> {
    let future_val = ctx.vreg_values[&future];

    // Try to use the monoio-direct polling function
    let poll_id = ctx.runtime_funcs.get("rt_monoio_poll").copied();

    if let Some(poll_id) = poll_id {
        // Call rt_monoio_poll(future) -> result or PENDING_MARKER
        let poll_ref = ctx.module.declare_func_in_func(poll_id, builder.func);
        let poll_call = builder.ins().call(poll_ref, &[future_val]);
        let poll_result = builder.inst_results(poll_call)[0];

        // Check if result is PENDING_MARKER (-1)
        let pending_marker = builder.ins().iconst(types::I64, -1);
        let is_pending = builder.ins().icmp(
            cranelift_codegen::ir::condcodes::IntCC::Equal,
            poll_result,
            pending_marker,
        );

        // Create blocks for pending and ready paths
        let pending_block = builder.create_block();
        let ready_block = builder.create_block();
        let merge_block = builder.create_block();

        builder.ins().brif(is_pending, pending_block, &[], ready_block, &[]);

        // Pending path: save state and return
        builder.switch_to_block(pending_block);
        builder.seal_block(pending_block);

        // Check if we have async state map for state machine
        if let Some(async_state_map) = ctx.async_state_map.as_ref() {
            if let Some(state) = async_state_map.get(&mir_block_id) {
                // Save live variables to MonoioFuture context
                let get_ctx_id = ctx.runtime_funcs.get("rt_monoio_future_get_ctx").copied();
                if let Some(get_ctx_id) = get_ctx_id {
                    let get_ctx_ref = ctx.module.declare_func_in_func(get_ctx_id, builder.func);
                    let call = builder.ins().call(get_ctx_ref, &[future_val]);
                    let ctx_val = builder.inst_results(call)[0];

                    let push_id = ctx.runtime_funcs["rt_array_push"];
                    let push_ref = ctx.module.declare_func_in_func(push_id, builder.func);
                    for reg in &state.live_after_await {
                        if let Some(val) = ctx.vreg_values.get(reg) {
                            let _ = builder.ins().call(push_ref, &[ctx_val, *val]);
                        }
                    }
                }

                // Set next state on MonoioFuture
                let set_state_id = ctx.runtime_funcs.get("rt_monoio_future_set_async_state").copied();
                if let Some(set_state_id) = set_state_id {
                    let set_state_ref = ctx.module.declare_func_in_func(set_state_id, builder.func);
                    let next_state = builder.ins().iconst(types::I64, (state.state_id + 1) as i64);
                    let _ = builder.ins().call(set_state_ref, &[future_val, next_state]);
                }
            }
        }

        // Return the future itself (suspended)
        builder.ins().return_(&[future_val]);

        // Ready path: result is in poll_result
        builder.switch_to_block(ready_block);
        builder.seal_block(ready_block);

        // Get the actual result from the future
        let get_result_id = ctx.runtime_funcs.get("rt_monoio_future_get_result").copied();
        let result = if let Some(get_result_id) = get_result_id {
            let get_result_ref = ctx.module.declare_func_in_func(get_result_id, builder.func);
            let call = builder.ins().call(get_result_ref, &[future_val]);
            builder.inst_results(call)[0]
        } else {
            poll_result
        };

        builder.ins().jump(merge_block, &[result]);

        // Merge block
        builder.switch_to_block(merge_block);
        builder.append_block_param(merge_block, types::I64);
        let merged_result = builder.block_params(merge_block)[0];
        builder.seal_block(merge_block);

        ctx.vreg_values.insert(dest, merged_result);
        return Ok(());
    }

    // Fallback to standard await
    compile_await(ctx, builder, dest, future, mir_block_id, entry_block)
}
