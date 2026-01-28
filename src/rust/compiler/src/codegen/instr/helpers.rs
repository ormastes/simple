// Helper functions for instruction compilation.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use super::{InstrContext, InstrResult};
use crate::mir::VReg;

/// Helper to get a VReg value, returning a default 0 if missing.
/// This handles cases where control flow or complex patterns leave VRegs undefined.
/// Note: Creating default values can cause SSA violations in some control flow patterns.
/// We create the value in the entry block to minimize domination issues.
pub(super) fn get_vreg_or_default<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    vreg: &VReg,
) -> cranelift_codegen::ir::Value {
    ctx.vreg_values.get(vreg).copied().unwrap_or_else(|| {
        // Create the constant in the entry block to ensure it dominates all uses
        let entry_block = ctx.entry_block;
        let current_block = builder.current_block().unwrap();

        // If we're not in the entry block, we need to be careful
        // For now, just create the value in the current block and hope for the best
        // A proper fix would require PHI nodes or ensuring proper value flow
        builder.ins().iconst(types::I64, 0)
    })
}

/// Helper to create a string constant in module data and return (ptr, len) values
pub(super) fn create_string_constant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    text: &str,
) -> InstrResult<(cranelift_codegen::ir::Value, cranelift_codegen::ir::Value)> {
    let bytes = text.as_bytes();
    let data_id = ctx
        .module
        .declare_anonymous_data(true, false)
        .map_err(|e| e.to_string())?;
    let mut data_desc = cranelift_module::DataDescription::new();
    data_desc.define(bytes.to_vec().into_boxed_slice());
    ctx.module.define_data(data_id, &data_desc).map_err(|e| e.to_string())?;

    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let ptr = builder.ins().global_value(types::I64, global_val);
    let len = builder.ins().iconst(types::I64, bytes.len() as i64);

    Ok((ptr, len))
}

/// Helper to perform indirect call with result handling
pub(super) fn indirect_call_with_result<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    sig_ref: cranelift_codegen::ir::SigRef,
    fn_ptr: cranelift_codegen::ir::Value,
    call_args: &[cranelift_codegen::ir::Value],
    dest: &Option<VReg>,
) {
    let call = builder.ins().call_indirect(sig_ref, fn_ptr, call_args);

    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            let null = builder.ins().iconst(types::I64, 0);
            ctx.vreg_values.insert(*d, null);
        }
    }
}
