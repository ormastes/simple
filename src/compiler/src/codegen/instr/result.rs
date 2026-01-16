// Result/Option and error handling compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{BlockId, VReg};

use super::{InstrContext, InstrResult};

/// Allocate a 16-byte tagged object with discriminant and payload.
pub(super) fn alloc_tagged_object<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    discriminant: i64,
    payload: Option<VReg>,
) {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);

    let size = builder.ins().iconst(types::I64, 16);
    let call = builder.ins().call(alloc_ref, &[size]);
    let ptr = builder.inst_results(call)[0];

    let disc_val = builder.ins().iconst(types::I64, discriminant);
    builder.ins().store(MemFlags::new(), disc_val, ptr, 0);

    let payload_val = payload
        .map(|v| ctx.vreg_values[&v])
        .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
    builder.ins().store(MemFlags::new(), payload_val, ptr, 8);

    ctx.vreg_values.insert(dest, ptr);
}

pub(super) fn compile_try_unwrap<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    error_block: BlockId,
    error_dest: VReg,
) {
    let val = ctx.vreg_values[&value];
    let disc = builder.ins().load(types::I64, MemFlags::new(), val, 0);
    let zero = builder.ins().iconst(types::I64, 0);
    let is_error = builder
        .ins()
        .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, disc, zero);

    let success_block = builder.create_block();
    let err_block = *ctx.blocks.get(&error_block).unwrap();

    builder.ins().brif(is_error, err_block, &[], success_block, &[]);

    builder.switch_to_block(success_block);
    let payload = builder.ins().load(types::I64, MemFlags::new(), val, 8);
    ctx.vreg_values.insert(dest, payload);
    ctx.vreg_values.insert(error_dest, val);
}

pub(super) fn compile_option_some<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    alloc_tagged_object(ctx, builder, dest, 1, Some(value));
}

pub(super) fn compile_option_none<M: Module>(ctx: &mut InstrContext<'_, M>, builder: &mut FunctionBuilder, dest: VReg) {
    alloc_tagged_object(ctx, builder, dest, 0, None);
}

pub(super) fn compile_result_ok<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    alloc_tagged_object(ctx, builder, dest, 1, Some(value));
}

pub(super) fn compile_result_err<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    alloc_tagged_object(ctx, builder, dest, 0, Some(value));
}
