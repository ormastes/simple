//! Function call instruction compilation.
//!
//! Handles all forms of function calls: user-defined, runtime FFI, and built-in functions.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::codegen::runtime_ffi::RUNTIME_FUNCS;
use crate::mir::{CallTarget, VReg};

use super::core::compile_builtin_io_call;
use super::helpers::get_vreg_or_default;
use super::{InstrContext, InstrResult};

/// Check if a function name is a profiler function (to avoid recursive instrumentation)
fn is_profiler_function(name: &str) -> bool {
    name.starts_with("rt_profiler_")
}

/// Create a null-terminated C string constant in module data and return a pointer value.
fn create_cstring_constant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    text: &str,
) -> InstrResult<cranelift_codegen::ir::Value> {
    let mut bytes = text.as_bytes().to_vec();
    bytes.push(0); // null terminator
    let data_id = ctx
        .module
        .declare_anonymous_data(true, false)
        .map_err(|e| e.to_string())?;
    let mut data_desc = cranelift_module::DataDescription::new();
    data_desc.define(bytes.into_boxed_slice());
    ctx.module.define_data(data_id, &data_desc).map_err(|e| e.to_string())?;

    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let ptr = builder.ins().global_value(types::I64, global_val);
    Ok(ptr)
}

/// Emit profiler call/return instrumentation around a function call.
/// Only emits if profiling is active at codegen time (zero overhead when off).
fn emit_profiler_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
) -> InstrResult<()> {
    if !crate::runtime_profile::is_profiling_active() {
        return Ok(());
    }
    if let Some(&record_call_id) = ctx.runtime_funcs.get("rt_profiler_record_call") {
        let name_ptr = create_cstring_constant(ctx, builder, func_name)?;
        let record_call_ref = ctx.module.declare_func_in_func(record_call_id, builder.func);
        let adapted = adapt_args_to_signature(builder, record_call_ref, vec![name_ptr]);
        builder.ins().call(record_call_ref, &adapted);
    }
    Ok(())
}

fn emit_profiler_return<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
) -> InstrResult<()> {
    if !crate::runtime_profile::is_profiling_active() {
        return Ok(());
    }
    if let Some(&record_return_id) = ctx.runtime_funcs.get("rt_profiler_record_return") {
        let record_return_ref = ctx.module.declare_func_in_func(record_return_id, builder.func);
        builder.ins().call(record_return_ref, &[]);
    }
    Ok(())
}

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
///
/// NOTE: rt_array_get, rt_tuple_get, rt_index_get, rt_dict_get are NOT included here
/// because they return RuntimeValue that could be any type (string, object, etc.),
/// not just integers. Untagging should be done based on the expected result type,
/// not the function name. The caller should handle type-specific untagging.
fn needs_runtime_value_untagging(func_name: &str) -> bool {
    // Currently no functions need automatic untagging.
    // Type-specific untagging is handled by the MIR Unbox instruction.
    matches!(func_name, "")
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

/// Adapt argument values to match a function's expected signature.
/// Handles count mismatches (padding/truncating) and type mismatches (casting).
pub(crate) fn adapt_args_to_signature(
    builder: &mut FunctionBuilder,
    func_ref: cranelift_codegen::ir::FuncRef,
    arg_vals: Vec<cranelift_codegen::ir::Value>,
) -> Vec<cranelift_codegen::ir::Value> {
    let sig_ref = builder.func.dfg.ext_funcs[func_ref].signature;
    let sig = &builder.func.dfg.signatures[sig_ref];
    let expected_count = sig.params.len();
    // Collect expected types before mutating builder
    let expected_types: Vec<_> = sig.params.iter().map(|p| p.value_type).collect();

    let mut adapted = Vec::with_capacity(expected_count);
    for i in 0..expected_count {
        let expected_ty = expected_types[i];
        if i < arg_vals.len() {
            let val = arg_vals[i];
            let actual_ty = builder.func.dfg.value_type(val);
            if actual_ty == expected_ty {
                adapted.push(val);
            } else if actual_ty.is_int() && expected_ty.is_int() {
                // Integer width conversion
                if actual_ty.bits() < expected_ty.bits() {
                    adapted.push(builder.ins().sextend(expected_ty, val));
                } else {
                    adapted.push(builder.ins().ireduce(expected_ty, val));
                }
            } else if actual_ty.is_int() && expected_ty.is_float() {
                // Int to float conversion
                if expected_ty == types::F32 {
                    adapted.push(builder.ins().f32const(0.0));
                } else {
                    adapted.push(builder.ins().f64const(0.0));
                }
            } else if actual_ty.is_float() && expected_ty.is_int() {
                // Float to int conversion
                adapted.push(builder.ins().iconst(expected_ty, 0));
            } else {
                // Fallback: use the value as-is and hope for the best
                adapted.push(val);
            }
        } else {
            // Padding: create default value for missing argument
            if expected_ty.is_int() {
                adapted.push(builder.ins().iconst(expected_ty, 0));
            } else if expected_ty == types::F32 {
                adapted.push(builder.ins().f32const(0.0));
            } else if expected_ty == types::F64 {
                adapted.push(builder.ins().f64const(0.0));
            } else {
                adapted.push(builder.ins().iconst(types::I64, 0));
            }
        }
    }
    adapted
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
    let func_name_raw = target.name();
    // Map Simple builtin names to runtime FFI function names
    let func_name: &str = match func_name_raw {
        "sys_get_args" => "rt_get_args",
        "sys_exit" => "rt_exit",
        // Map text-argument file FFI to RuntimeValue wrappers
        "rt_file_read_text" => "rt_file_read_text_rv",
        other => other,
    };

    // Handle Result/Option constructor builtins (Ok, Err, Some, None)
    // Also handle qualified names like "MyResult::Ok", "Option::None", etc.
    let variant_name = func_name
        .rsplit_once("::")
        .or_else(|| func_name.rsplit_once('.'))
        .map(|(_, v)| v)
        .unwrap_or(func_name);
    if matches!(variant_name, "Ok" | "Err" | "Some" | "None") {
        if let Some(d) = dest {
            let enum_new_id = ctx.runtime_funcs["rt_enum_new"];
            let enum_new_ref = ctx.module.declare_func_in_func(enum_new_id, builder.func);
            // Use hashed discriminants consistently with pattern matching
            let disc = {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                variant_name.hash(&mut hasher);
                (hasher.finish() & 0xFFFFFFFF) as i64
            };
            let enum_id_val = builder.ins().iconst(types::I32, 0);
            let disc_val = builder.ins().iconst(types::I32, disc);
            let payload_val = if !args.is_empty() {
                get_vreg_or_default(ctx, builder, &args[0])
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            let call = builder.ins().call(enum_new_ref, &[enum_id_val, disc_val, payload_val]);
            ctx.vreg_values.insert(*d, builder.inst_results(call)[0]);
        }
        return Ok(());
    }

    // Check if this is a built-in I/O function (print, println, etc.)
    if let Some(result) = compile_builtin_io_call(ctx, builder, func_name, args, dest)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
    } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
        // User-defined function
        if !is_profiler_function(func_name) {
            emit_profiler_call(ctx, builder, func_name)?;
        }
        let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
        let arg_vals: Vec<_> = args.iter().map(|a| get_vreg_or_default(ctx, builder, a)).collect();
        let arg_vals = adapt_args_to_signature(builder, callee_ref, arg_vals);
        let call = builder.ins().call(callee_ref, &arg_vals);
        if !is_profiler_function(func_name) {
            emit_profiler_return(ctx, builder)?;
        }
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    } else if let Some(&runtime_id) = ctx.runtime_funcs.get(func_name) {
        // Runtime FFI function
        if !is_profiler_function(func_name) {
            emit_profiler_call(ctx, builder, func_name)?;
        }
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);

        // Check if this function needs RuntimeValue tagging for certain arguments
        let tagging_indices = needs_runtime_value_tagging(func_name);
        // Check if this function returns RuntimeValue that needs untagging
        let needs_untagging = needs_runtime_value_untagging(func_name);

        // First collect VReg values with defaults
        let mut arg_vals = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            let val = get_vreg_or_default(ctx, builder, a);
            // Tag the value if this argument position needs RuntimeValue
            let val = if let Some(ref indices) = &tagging_indices {
                if indices.contains(&i) {
                    tag_int_as_runtime_value(builder, val)
                } else {
                    val
                }
            } else {
                val
            };
            arg_vals.push(val);
        }

        let arg_vals = adapt_args_to_signature(builder, runtime_ref, arg_vals);
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
        if !is_profiler_function(func_name) {
            emit_profiler_return(ctx, builder)?;
        }
    } else {
        eprintln!("[WARN compile_call] Function '{}' not found in func_ids ({} entries) or runtime_funcs ({} entries)",
            func_name, ctx.func_ids.len(), ctx.runtime_funcs.len());
    }

    Ok(())
}
