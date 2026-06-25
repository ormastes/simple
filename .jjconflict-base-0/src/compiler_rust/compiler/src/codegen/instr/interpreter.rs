//! Interpreter-specific instruction compilation.
//!
//! Handles instructions that interact with the interpreter runtime:
//! - InterpEval: evaluates expressions in the interpreter
//! - ContractOldCapture: captures values for postcondition 'old' expressions

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::call_runtime_1;
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
    let idx = builder.ins().iconst(types::I64, expr_index as i64);
    let result = call_runtime_1(ctx, builder, "rt_interp_eval", idx);
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
