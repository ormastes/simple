//! Function call instruction compilation.
//!
//! Handles all forms of function calls: user-defined, runtime FFI, and built-in functions.

use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{CallTarget, VReg};

use super::core::compile_builtin_io_call;
use super::{InstrContext, InstrResult};

/// Compile Call instruction: dispatches to user-defined, built-in I/O, or runtime FFI functions
///
/// This handles three types of function calls:
/// 1. Built-in I/O functions (print, println, etc.) - handled via compile_builtin_io_call
/// 2. User-defined functions - looked up in func_ids
/// 3. Runtime FFI functions - looked up in runtime_funcs
pub fn compile_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    target: &CallTarget,
    args: &[VReg],
) -> InstrResult<()> {
    let func_name = target.name();

    // Check if this is a built-in I/O function (print, println, etc.)
    if let Some(result) = compile_builtin_io_call(ctx, builder, func_name, args, dest)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
    } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
        // User-defined function
        let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
        let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
        let call = builder.ins().call(callee_ref, &arg_vals);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    } else if let Some(&runtime_id) = ctx.runtime_funcs.get(func_name) {
        // Runtime FFI function
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
        let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
        let call = builder.ins().call(runtime_ref, &arg_vals);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    }

    Ok(())
}
