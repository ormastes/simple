//! Actor instruction compilation
//!
//! This module handles compilation of actor-related instructions:
//! - ActorSend - Send a message to an actor
//! - ActorRecv - Receive a message from the actor's mailbox
//! - ActorJoin - Wait for an actor to complete
//! - ActorReply - Reply to a message
//! - Await - Await a future result

use cranelift_codegen::ir::types;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::adapted_call;
use super::{InstrContext, InstrResult};

/// Compile ActorSend instruction
pub fn compile_actor_send<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    actor: VReg,
    message: VReg,
) -> InstrResult<()> {
    let send_id = ctx.runtime_funcs["rt_actor_send"];
    let send_ref = ctx.module.declare_func_in_func(send_id, builder.func);
    let actor_val = ctx.get_vreg(&actor)?;
    let msg_val = ctx.get_vreg(&message)?;
    adapted_call(builder, send_ref, &[actor_val, msg_val]);
    Ok(())
}

/// Compile ActorRecv instruction
pub fn compile_actor_recv<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
) -> InstrResult<()> {
    let recv_id = ctx.runtime_funcs["rt_actor_recv"];
    let recv_ref = ctx.module.declare_func_in_func(recv_id, builder.func);
    let call = adapted_call(builder, recv_ref, &[]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile ActorJoin instruction
pub fn compile_actor_join<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    actor: VReg,
) -> InstrResult<()> {
    let join_id = ctx.runtime_funcs["rt_actor_join"];
    let join_ref = ctx.module.declare_func_in_func(join_id, builder.func);
    let actor_val = ctx.get_vreg(&actor)?;
    let call = adapted_call(builder, join_ref, &[actor_val]);
    let raw_result = builder.inst_results(call)[0];
    // Convert i64 to RuntimeValue by tagging (shift left 3 bits)
    let tagged_result = builder.ins().ishl_imm(raw_result, 3);
    ctx.vreg_values.insert(dest, tagged_result);
    Ok(())
}

/// Compile ActorReply instruction
pub fn compile_actor_reply<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    message: VReg,
) -> InstrResult<()> {
    let reply_id = ctx.runtime_funcs["rt_actor_reply"];
    let reply_ref = ctx.module.declare_func_in_func(reply_id, builder.func);
    let message_val = ctx.get_vreg(&message)?;
    adapted_call(builder, reply_ref, &[message_val]);
    // Reply returns RuntimeValue (NIL), but we don't need to store it
    // The result is handled by the ConstNil instruction that follows
    Ok(())
}

/// Compile Await instruction
pub fn compile_await<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    future: VReg,
) -> InstrResult<()> {
    let await_id = ctx.runtime_funcs["rt_future_await"];
    let await_ref = ctx.module.declare_func_in_func(await_id, builder.func);
    let future_val = ctx.get_vreg(&future)?;
    let call = adapted_call(builder, await_ref, &[future_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile GeneratorNext instruction
pub fn compile_generator_next<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    generator: VReg,
) -> InstrResult<()> {
    let next_id = ctx.runtime_funcs["rt_generator_next"];
    let next_ref = ctx.module.declare_func_in_func(next_id, builder.func);
    let gen_val = ctx.get_vreg(&generator)?;
    let call = adapted_call(builder, next_ref, &[gen_val]);
    let result = builder.inst_results(call)[0];

    // The runtime returns a tagged RuntimeValue; unwrap to a raw i64 for
    // downstream arithmetic in codegen paths.
    let unwrap_id = ctx.runtime_funcs["rt_value_as_int"];
    let unwrap_ref = ctx.module.declare_func_in_func(unwrap_id, builder.func);
    let unwrap_call = adapted_call(builder, unwrap_ref, &[result]);
    let unwrapped = builder.inst_results(unwrap_call)[0];
    ctx.vreg_values.insert(dest, unwrapped);
    Ok(())
}
