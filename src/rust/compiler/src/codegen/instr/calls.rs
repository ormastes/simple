//! Function call instruction compilation.
//!
//! Handles all forms of function calls: user-defined, runtime FFI, and built-in functions.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::codegen::runtime_ffi::RUNTIME_FUNCS;
use crate::mir::{CallTarget, VReg};

use super::core::compile_builtin_io_call;
use super::{InstrContext, InstrResult};

/// Get the return type for a runtime FFI function.
/// Returns None if the function is not found or has no return value.
fn get_runtime_return_type(func_name: &str) -> Option<types::Type> {
    RUNTIME_FUNCS
        .iter()
        .find(|spec| spec.name == func_name)
        .and_then(|spec| spec.returns.first().copied())
}

/// Check if a function needs RuntimeValue tagging for certain argument positions.
/// Currently disabled - tagging must be done at MIR level with type information.
///
/// The issue is that at codegen time we don't know if a value is:
/// - A native integer (needs tagging: value << 3)
/// - A heap object like string/array (already RuntimeValue, tagging would corrupt)
/// - A float (needs different tagging)
///
/// NOTE: MirInst::BoxInt is now implemented and inserted during MIR lowering
/// in lowering_expr.rs when passing native integers to FFI functions.
fn needs_runtime_value_tagging(_func_name: &str) -> Option<Vec<usize>> {
    // Disabled - tagging is done at MIR level via MirInst::BoxInt
    None
}

/// Tag an integer value as RuntimeValue: (value << 3) | TAG_INT
/// TAG_INT is 0, so this is equivalent to value << 3
fn tag_int_as_runtime_value(
    builder: &mut FunctionBuilder,
    value: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let three = builder.ins().iconst(types::I64, 3);
    builder.ins().ishl(value, three)
}

/// Check if a runtime function returns a RuntimeValue that should be untagged to raw i64.
/// These are functions that return RuntimeValue containing integers that need to be extracted.
fn needs_runtime_value_untagging(func_name: &str) -> bool {
    matches!(
        func_name,
        "rt_array_get" | "rt_tuple_get" | "rt_index_get" | "rt_dict_get"
    )
}

/// Untag a RuntimeValue to raw i64 by right-shifting 3 bits.
/// RuntimeValue integers are encoded as (value << 3) | TAG_INT where TAG_INT = 0.
/// So untagging is simply value >> 3 (arithmetic shift).
#[allow(dead_code)]
fn untag_runtime_value_to_int(
    builder: &mut FunctionBuilder,
    value: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let three = builder.ins().iconst(types::I64, 3);
    builder.ins().sshr(value, three)
}

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

        // Check if this function needs RuntimeValue tagging for certain arguments
        let tagging_indices = needs_runtime_value_tagging(func_name);
        // Check if this function returns RuntimeValue that needs untagging
        let needs_untagging = needs_runtime_value_untagging(func_name);

        let arg_vals: Vec<_> = args
            .iter()
            .enumerate()
            .map(|(i, a)| {
                let val = ctx.vreg_values[a];
                // Tag the value if this argument position needs RuntimeValue
                if let Some(ref indices) = tagging_indices {
                    if indices.contains(&i) {
                        return tag_int_as_runtime_value(builder, val);
                    }
                }
                val
            })
            .collect();

        let call = builder.ins().call(runtime_ref, &arg_vals);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                let mut result = results[0];

                // Extend smaller return types to i64 (the standard vreg type)
                // This is needed because some FFI functions return i32 (e.g., rt_exec)
                // but all vregs are expected to be i64
                if let Some(ret_type) = get_runtime_return_type(func_name) {
                    if ret_type == types::I32 {
                        // Sign-extend i32 to i64 (for exit codes and status values)
                        result = builder.ins().sextend(types::I64, result);
                    } else if ret_type == types::I8 {
                        // Sign-extend i8 to i64
                        result = builder.ins().sextend(types::I64, result);
                    }
                }

                // Untag the result if needed
                let final_result = if needs_untagging {
                    untag_runtime_value_to_int(builder, result)
                } else {
                    result
                };
                ctx.vreg_values.insert(*d, final_result);
            }
        }
    }

    Ok(())
}
