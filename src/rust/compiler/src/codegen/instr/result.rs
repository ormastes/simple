// Result/Option and error handling compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{BlockId, VReg};

use super::helpers::get_vreg_or_default;
use super::{InstrContext, InstrResult};

/// Create a Result/Option enum using rt_enum_new for consistent representation.
/// This ensures rt_enum_discriminant and rt_enum_payload work correctly.
///
/// Convention:
/// - Result: enum_id=0, Ok=discriminant 1, Err=discriminant 0
/// - Option: enum_id=1, Some=discriminant 1, None=discriminant 0
fn create_enum_value<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    enum_id: i64,
    discriminant: i64,
    payload: Option<VReg>,
) {
    let enum_new_id = ctx.runtime_funcs["rt_enum_new"];
    let enum_new_ref = ctx.module.declare_func_in_func(enum_new_id, builder.func);

    let enum_id_val = builder.ins().iconst(types::I32, enum_id);
    let disc_val = builder.ins().iconst(types::I32, discriminant);
    let payload_val = payload
        .map(|v| get_vreg_or_default(ctx, builder, &v))
        .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));

    let call = builder.ins().call(enum_new_ref, &[enum_id_val, disc_val, payload_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

pub(super) fn compile_try_unwrap<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    error_block: BlockId,
    error_dest: VReg,
) {
    let val = get_vreg_or_default(ctx, builder, &value);

    // Use rt_enum_discriminant to check if Ok (1) or Err (0)
    let disc_id = ctx.runtime_funcs["rt_enum_discriminant"];
    let disc_ref = ctx.module.declare_func_in_func(disc_id, builder.func);
    let disc_call = builder.ins().call(disc_ref, &[val]);
    let disc = builder.inst_results(disc_call)[0];

    let zero = builder.ins().iconst(types::I64, 0);
    let is_error = builder
        .ins()
        .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, disc, zero);

    let success_block = builder.create_block();
    let err_block = *ctx.blocks.get(&error_block).unwrap();

    builder.ins().brif(is_error, err_block, &[], success_block, &[]);

    builder.switch_to_block(success_block);
    // Use rt_enum_payload to extract the payload
    let payload_id = ctx.runtime_funcs["rt_enum_payload"];
    let payload_ref = ctx.module.declare_func_in_func(payload_id, builder.func);
    let payload_call = builder.ins().call(payload_ref, &[val]);
    let payload = builder.inst_results(payload_call)[0];
    ctx.vreg_values.insert(dest, payload);
    ctx.vreg_values.insert(error_dest, val);
}

pub(super) fn compile_option_some<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    create_enum_value(ctx, builder, dest, 1, 1, Some(value)); // Option enum_id=1, Some=1
}

pub(super) fn compile_option_none<M: Module>(ctx: &mut InstrContext<'_, M>, builder: &mut FunctionBuilder, dest: VReg) {
    create_enum_value(ctx, builder, dest, 1, 0, None); // Option enum_id=1, None=0
}

pub(super) fn compile_result_ok<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    create_enum_value(ctx, builder, dest, 0, 1, Some(value)); // Result enum_id=0, Ok=1
}

pub(super) fn compile_result_err<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) {
    create_enum_value(ctx, builder, dest, 0, 0, Some(value)); // Result enum_id=0, Err=0
}
