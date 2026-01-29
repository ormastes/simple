// Contract checking instruction compilation.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{ContractKind, VReg};

use super::helpers::create_string_constant;
use super::{InstrContext, InstrResult};

/// Compile a contract check instruction.
/// This checks the condition and calls a runtime function to panic if it fails.
pub(crate) fn compile_contract_check<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    condition: VReg,
    kind: ContractKind,
    func_name: &str,
    _message: Option<&str>,
) -> InstrResult<()> {
    let cond = ctx.vreg_values[&condition];

    // Get the kind as an integer for the runtime call
    let kind_val = match kind {
        ContractKind::Precondition => 0i64,
        ContractKind::Postcondition => 1i64,
        ContractKind::ErrorPostcondition => 2i64,
        ContractKind::InvariantEntry => 3i64,
        ContractKind::InvariantExit => 4i64,
        ContractKind::Assertion => 5i64,
    };

    // Check if we have the runtime contract check function
    if let Some(&func_id) = ctx.runtime_funcs.get("simple_contract_check") {
        // Call runtime: simple_contract_check(condition: bool, kind: i64, func_name_ptr: *const u8, func_name_len: i64)
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

        // Create string data for function name and get (ptr, len) values
        let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

        // Convert bool condition to i64 for the call
        let cond_i64 = builder.ins().uextend(types::I64, cond);
        let kind_iconst = builder.ins().iconst(types::I64, kind_val);

        builder
            .ins()
            .call(func_ref, &[cond_i64, kind_iconst, name_ptr, name_len]);
    } else {
        // Fallback: generate inline check with trap on failure
        // Create a conditional branch that traps if the condition is false
        let trap_block = builder.create_block();
        let continue_block = builder.create_block();

        // Branch based on condition
        builder.ins().brif(cond, continue_block, &[], trap_block, &[]);

        // Trap block - triggers a panic
        builder.switch_to_block(trap_block);
        builder.seal_block(trap_block);
        builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::unwrap_user(kind_val as u8));

        // Continue block - normal execution
        builder.switch_to_block(continue_block);
        builder.seal_block(continue_block);
    }
    Ok(())
}
