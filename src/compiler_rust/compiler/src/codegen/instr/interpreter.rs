//! Interpreter-specific instruction compilation.
//!
//! Handles instructions that interact with the interpreter runtime:
//! - InterpEval: evaluates expressions in the interpreter
//! - ContractOldCapture: captures values for postcondition 'old' expressions

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::adapted_call;
use super::{InstrContext, InstrResult};

/// Compile InterpEval instruction: evaluates an expression in the interpreter
///
/// This is used when codegen encounters an expression that can't be compiled
/// directly (e.g., certain runtime-only features). The expression is evaluated
/// by calling the interpreter's eval function.
pub fn compile_interp_eval<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    expr_index: usize,
) -> InstrResult<()> {
    let interp_eval_id = ctx.runtime_funcs["rt_interp_eval"];
    let interp_eval_ref = ctx.module.declare_func_in_func(interp_eval_id, builder.func);
    let idx = builder.ins().iconst(types::I64, expr_index as i64);
    let call = adapted_call(builder, interp_eval_ref, &[idx]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile ContractOldCapture instruction: captures value for 'old' expressions in postconditions
///
/// Simply copies the value to the destination register. The actual capture happens at function
/// entry before any state changes occur.
pub fn compile_contract_old_capture<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
) -> InstrResult<()> {
    let val = ctx.get_vreg(&value)?;
    ctx.vreg_values.insert(dest, val);
    Ok(())
}
