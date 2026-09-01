//! Coverage instrumentation instruction compilation.
//!
//! Handles MC/DC (Modified Condition/Decision Coverage) probe instructions for runtime coverage collection.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::helpers::{call_runtime_2_void, call_runtime_5_void, call_runtime_6_void, create_cstring_constant};
use super::{InstrContext, InstrResult};

/// Compile DecisionProbe instruction: records decision outcome for MC/DC coverage
///
/// Calls the core-C coverage ABI with a real source owner and span.
pub fn compile_decision_probe<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    result: VReg,
    decision_id: u32,
    file: &str,
    line: u32,
    column: u32,
) -> InstrResult<()> {
    let result_val = match ctx.vreg_values.get(&result) {
        Some(&v) => v,
        None => {
            return Err(format!("DecisionProbe: result vreg {:?} not found", result));
        }
    };

    let decision_id_val = builder.ins().iconst(types::I32, decision_id as i64);
    let file_value = create_cstring_constant(ctx, builder, file)?;
    let line_value = builder.ins().iconst(types::I32, line as i64);
    let column_value = builder.ins().iconst(types::I32, column as i64);
    call_runtime_5_void(
        ctx,
        builder,
        "rt_coverage_decision_probe",
        decision_id_val,
        result_val,
        file_value,
        line_value,
        column_value,
    );

    Ok(())
}

/// Compile ConditionProbe instruction: records individual condition outcome in a decision
///
/// Calls the core-C coverage ABI with a real source owner and span.
#[allow(clippy::too_many_arguments)] // reason: ABI-locked or codegen entry signature; refactoring would break caller contract
pub fn compile_condition_probe<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    decision_id: u32,
    condition_id: u32,
    result: VReg,
    file: &str,
    line: u32,
    column: u32,
) -> InstrResult<()> {
    let result_val = match ctx.vreg_values.get(&result) {
        Some(&v) => v,
        None => {
            return Err(format!("ConditionProbe: result vreg {:?} not found", result));
        }
    };

    let decision_id_val = builder.ins().iconst(types::I32, decision_id as i64);
    let condition_id_val = builder.ins().iconst(types::I32, condition_id as i64);
    let file_value = create_cstring_constant(ctx, builder, file)?;
    let line_value = builder.ins().iconst(types::I32, line as i64);
    let column_value = builder.ins().iconst(types::I32, column as i64);
    call_runtime_6_void(
        ctx,
        builder,
        "rt_coverage_condition_probe",
        decision_id_val,
        condition_id_val,
        result_val,
        file_value,
        line_value,
        column_value,
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
    call_runtime_2_void(ctx, builder, "rt_path_probe", path_id_val, block_id_val);

    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn cranelift_coverage_keeps_core_c_owner_and_span_abi() {
        // Restrict the scan to production code so this test's own literal
        // expectations cannot make a deleted probe path appear present.
        let source = include_str!("coverage.rs");
        let production = source.split("#[cfg(test)]").next().expect("test marker");
        for name in ["decision", "condition"] {
            let required = format!("\"rt_coverage_{}_probe\"", name);
            assert!(production.contains(&required), "missing core-C {} probe", name);
            let legacy = format!("\"rt_{}_probe\"", name);
            assert!(
                !production.contains(&legacy),
                "legacy {} probe loses the source owner and span",
                name
            );
        }
        assert!(
            production.contains("create_cstring_constant(ctx, builder, file)?")
                && production.contains("line as i64")
                && production.contains("column as i64"),
            "coverage probes must retain NUL-terminated file, line, and column"
        );
    }
}
