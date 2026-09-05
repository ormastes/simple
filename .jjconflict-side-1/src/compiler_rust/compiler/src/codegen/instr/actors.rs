//! Actor instruction compilation
//!
//! This module handles compilation of actor-related instructions:
//! - ActorSend - Send a message to an actor
//! - ActorRecv - Receive a message from the actor's mailbox
//! - ActorJoin - Wait for an actor to complete
//! - ActorReply - Reply to a message
//! - Await - Await a future result

use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::{adapted_call, call_runtime_1, call_runtime_1_void, call_runtime_2_void};
use super::{InstrContext, InstrResult};

/// Compile ActorSend instruction
pub fn compile_actor_send<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    actor: VReg,
    message: VReg,
) -> InstrResult<()> {
    let actor_val = ctx.get_vreg(&actor)?;
    let msg_val = ctx.get_vreg(&message)?;
    call_runtime_2_void(ctx, builder, "rt_actor_send", actor_val, msg_val);
    Ok(())
}

/// Compile ActorRecv instruction — arity-0 with return value (open-coded)
pub fn compile_actor_recv<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
) -> InstrResult<()> {
    let recv_id = *ctx
        .runtime_funcs
        .get("rt_actor_recv")
        .unwrap_or_else(|| panic!("missing runtime fn 'rt_actor_recv' in {}", ctx.func.name));
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
    let actor_val = ctx.get_vreg(&actor)?;
    let raw_result = call_runtime_1(ctx, builder, "rt_actor_join", actor_val);
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
    let message_val = ctx.get_vreg(&message)?;
    call_runtime_1_void(ctx, builder, "rt_actor_reply", message_val);
    Ok(())
}

/// Compile Await instruction
pub fn compile_await<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    future: VReg,
) -> InstrResult<()> {
    let future_val = ctx.get_vreg(&future)?;
    let result = call_runtime_1(ctx, builder, "rt_future_await", future_val);
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
    let gen_val = ctx.get_vreg(&generator)?;
    let result = call_runtime_1(ctx, builder, "rt_generator_next", gen_val);

    // The runtime returns a tagged RuntimeValue; unwrap to a raw i64 for
    // downstream arithmetic in codegen paths.
    let unwrapped = call_runtime_1(ctx, builder, "rt_value_as_int", result);
    ctx.vreg_values.insert(dest, unwrapped);
    Ok(())
}
