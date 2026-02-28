//! Coverage instrumentation instruction compilation.
//!
//! Handles MC/DC (Modified Condition/Decision Coverage) probe instructions for runtime coverage collection.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::adapted_call;
use super::{InstrContext, InstrResult};

/// Compile DecisionProbe instruction: records decision outcome for MC/DC coverage
///
/// Calls rt_decision_probe(decision_id, result) to track which boolean outcomes
/// a decision expression evaluates to during execution.
pub fn compile_decision_probe<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    result: VReg,
    decision_id: u32,
    _file: &str,
    _line: u32,
    _column: u32,
) -> InstrResult<()> {
    let result_val = match ctx.vreg_values.get(&result) {
        Some(&v) => v,
        None => {
            return Err(format!("DecisionProbe: result vreg {:?} not found", result));
        }
    };

    let decision_id_val = builder.ins().iconst(types::I64, decision_id as i64);
    let probe_func_id = ctx.runtime_funcs["rt_decision_probe"];
    let probe_func_ref = ctx.module.declare_func_in_func(probe_func_id, builder.func);
    adapted_call(builder, probe_func_ref, &[decision_id_val, result_val]);

    Ok(())
}

/// Compile ConditionProbe instruction: records individual condition outcome in a decision
///
/// Calls rt_condition_probe(decision_id, condition_id, result) to track which conditions
/// within a complex decision (e.g., A && B || C) independently affect the outcome.
pub fn compile_condition_probe<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    decision_id: u32,
    condition_id: u32,
    result: VReg,
    _file: &str,
    _line: u32,
    _column: u32,
) -> InstrResult<()> {
    let result_val = match ctx.vreg_values.get(&result) {
        Some(&v) => v,
        None => {
            return Err(format!("ConditionProbe: result vreg {:?} not found", result));
        }
    };

    let decision_id_val = builder.ins().iconst(types::I64, decision_id as i64);
    let condition_id_val = builder.ins().iconst(types::I32, condition_id as i64);
    let probe_func_id = ctx.runtime_funcs["rt_condition_probe"];
    let probe_func_ref = ctx.module.declare_func_in_func(probe_func_id, builder.func);
    adapted_call(
        builder,
        probe_func_ref,
        &[decision_id_val, condition_id_val, result_val],
    );

    Ok(())
}

/// Compile PathProbe instruction: records execution path through control flow
///
/// Calls rt_path_probe(path_id, block_id) to track which basic blocks are executed.
pub fn compile_path_probe<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    path_id: u32,
    block_id: u32,
) -> InstrResult<()> {
    let path_id_val = builder.ins().iconst(types::I64, path_id as i64);
    let block_id_val = builder.ins().iconst(types::I32, block_id as i64);
    let probe_func_id = ctx.runtime_funcs["rt_path_probe"];
    let probe_func_ref = ctx.module.declare_func_in_func(probe_func_id, builder.func);
    adapted_call(builder, probe_func_ref, &[path_id_val, block_id_val]);

    Ok(())
}
