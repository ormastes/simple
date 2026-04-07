// Builtin method compilation for codegen.

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, Signature};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use super::super::shared::platform_call_conv;
use super::helpers::{adapted_call, declare_named_bytes, get_vreg_or_default};
use super::{InstrContext, InstrResult};
use crate::mir::VReg;

/// Helper to call a runtime function and get its result
fn call_runtime_1<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg]);
    builder.inst_results(call)[0]
}

/// Helper to call a runtime function with 2 args and get its result
fn call_runtime_2<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2]);
    builder.inst_results(call)[0]
}

/// Helper to call a runtime function with 2 args that returns void
fn call_runtime_2_void<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
) {
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    adapted_call(builder, func_ref, &[arg1, arg2]);
}

/// Helper to call a runtime function with 3 args and get its result
fn call_runtime_3<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg1: cranelift_codegen::ir::Value,
    arg2: cranelift_codegen::ir::Value,
    arg3: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = adapted_call(builder, func_ref, &[arg1, arg2, arg3]);
    builder.inst_results(call)[0]
}

/// Pass value through for array/dict operations.
/// Values that are already RuntimeValue (strings, arrays, objects) should be passed directly.
/// For .push() on integer-typed arrays, MIR lowering now inserts BoxInt before the
/// MethodCallStatic (see lowering_expr.rs), so integer args arrive already tagged.
/// This function remains a no-op pass-through.
fn wrap_value<M: Module>(
    _ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    val
}

/// Call a len method with fallback to 0 if not present
fn call_len_method<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    receiver: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    if let Some(&len_id) = ctx.runtime_funcs.get(func_name) {
        let len_ref = ctx.module.declare_func_in_func(len_id, builder.func);
        let call = adapted_call(builder, len_ref, &[receiver]);
        builder.inst_results(call)[0]
    } else {
        builder.ins().iconst(types::I64, 0)
    }
}

pub(crate) fn compile_builtin_method<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    receiver_type: &str,
    method: &str,
    args: &[VReg],
) -> InstrResult<()> {
    let receiver_val = ctx.get_vreg(&receiver)?;
    let result = match (receiver_type, method) {
        ("Array", "push") | ("array", "push") => {
            let arg_val = ctx.get_vreg(&args[0])?;
            let wrapped = wrap_value(ctx, builder, arg_val);
            call_runtime_2_void(ctx, builder, "rt_array_push", receiver_val, wrapped);
            // push() modifies in-place and returns the receiver for chaining
            Some(receiver_val)
        }
        ("Array", "len") | ("array", "len") => Some(call_len_method(ctx, builder, "rt_array_len", receiver_val)),
        ("Array", "get") | ("array", "get") => {
            let idx_val = ctx.get_vreg(&args[0])?;
            let wrapped_idx = wrap_value(ctx, builder, idx_val);
            Some(call_runtime_2(ctx, builder, "rt_index_get", receiver_val, wrapped_idx))
        }
        ("Array", "set") | ("array", "set") => {
            let idx_val = ctx.get_vreg(&args[0])?;
            let arg_val = ctx.get_vreg(&args[1])?;
            let wrapped_idx = wrap_value(ctx, builder, idx_val);
            let wrapped_val = wrap_value(ctx, builder, arg_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_index_set", receiver_val, wrapped_idx, wrapped_val);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("Array", "pop") | ("array", "pop") => Some(call_runtime_1(ctx, builder, "rt_array_pop", receiver_val)),
        ("Array", "clear") | ("array", "clear") => {
            let result_i8 = call_runtime_1(ctx, builder, "rt_array_clear", receiver_val);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("String", "len") | ("string", "len") => Some(call_len_method(ctx, builder, "rt_string_len", receiver_val)),
        ("String", "concat") | ("string", "concat") => {
            let arg_val = ctx.get_vreg(&args[0])?;
            Some(call_runtime_2(ctx, builder, "rt_string_concat", receiver_val, arg_val))
        }
        ("String", "starts_with") | ("string", "starts_with") => {
            let arg_val = ctx.get_vreg(&args[0])?;
            Some(call_runtime_2(
                ctx,
                builder,
                "rt_string_starts_with",
                receiver_val,
                arg_val,
            ))
        }
        ("String", "ends_with") | ("string", "ends_with") => {
            let arg_val = ctx.get_vreg(&args[0])?;
            Some(call_runtime_2(
                ctx,
                builder,
                "rt_string_ends_with",
                receiver_val,
                arg_val,
            ))
        }
        ("Dict", "get") | ("dict", "get") => {
            let key_val = ctx.get_vreg(&args[0])?;
            let wrapped_key = wrap_value(ctx, builder, key_val);
            Some(call_runtime_2(ctx, builder, "rt_index_get", receiver_val, wrapped_key))
        }
        ("Dict", "set") | ("dict", "set") => {
            let key_val = ctx.get_vreg(&args[0])?;
            let val_val = ctx.get_vreg(&args[1])?;
            let wrapped_key = wrap_value(ctx, builder, key_val);
            let wrapped_val = wrap_value(ctx, builder, val_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_dict_set", receiver_val, wrapped_key, wrapped_val);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("Dict", "len") | ("dict", "len") => Some(call_len_method(ctx, builder, "rt_dict_len", receiver_val)),
        ("Dict", "clear") | ("dict", "clear") => {
            let result_i8 = call_runtime_1(ctx, builder, "rt_dict_clear", receiver_val);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("Dict", "keys") | ("dict", "keys") => Some(call_runtime_1(ctx, builder, "rt_dict_keys", receiver_val)),
        ("Dict", "values") | ("dict", "values") => Some(call_runtime_1(ctx, builder, "rt_dict_values", receiver_val)),
        ("Tuple", "get") | ("tuple", "get") => {
            let idx_val = ctx.get_vreg(&args[0])?;
            Some(call_runtime_2(ctx, builder, "rt_tuple_get", receiver_val, idx_val))
        }
        ("Tuple", "len") | ("tuple", "len") => Some(call_len_method(ctx, builder, "rt_tuple_len", receiver_val)),
        ("Tuple", "set") | ("tuple", "set") => {
            let idx_val = ctx.get_vreg(&args[0])?;
            let arg_val = ctx.get_vreg(&args[1])?;
            let wrapped = wrap_value(ctx, builder, arg_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_tuple_set", receiver_val, idx_val, wrapped);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("Array", "contains")
        | ("array", "contains")
        | ("Dict", "contains")
        | ("dict", "contains")
        | ("String", "contains")
        | ("string", "contains") => {
            let arg_val = ctx.get_vreg(&args[0])?;
            let result_i8 = call_runtime_2(ctx, builder, "rt_contains", receiver_val, arg_val);
            Some(super::helpers::safe_extend_to_i64(builder, result_i8))
        }
        ("Array", "slice") | ("array", "slice") | ("String", "slice") | ("string", "slice") => {
            let slice_id = ctx.runtime_funcs["rt_slice"];
            let slice_ref = ctx.module.declare_func_in_func(slice_id, builder.func);
            let start = ctx.get_vreg(&args[0])?;
            let end = if args.len() > 1 {
                ctx.get_vreg(&args[1])?
            } else {
                builder.ins().iconst(types::I64, i64::MAX)
            };
            let step = if args.len() > 2 {
                ctx.get_vreg(&args[2])?
            } else {
                builder.ins().iconst(types::I64, 1)
            };
            let call = adapted_call(builder, slice_ref, &[receiver_val, start, end, step]);
            Some(builder.inst_results(call)[0])
        }
        _ => {
            // Try cross-module resolution before falling back to rt_method_not_found.
            // Build name variants to look up in use_map / import_map.
            let dot_name = format!("{}.{}", receiver_type, method);
            let lower_name = format!("{}_{}", receiver_type.to_lowercase(), method);
            let dunder_name = format!("{}__{}", receiver_type, method);

            let resolved_name = ctx
                .use_map
                .get(&dot_name)
                .or_else(|| ctx.import_map.get(&dot_name))
                .or_else(|| ctx.use_map.get(&dunder_name))
                .or_else(|| ctx.import_map.get(&dunder_name))
                .or_else(|| ctx.use_map.get(&lower_name))
                .or_else(|| ctx.import_map.get(&lower_name))
                .or_else(|| ctx.use_map.get(method))
                .or_else(|| ctx.import_map.get(method))
                .cloned();

            if let Some(resolved) = resolved_name {
                let resolved = if cfg!(target_os = "macos") && resolved.contains('.') {
                    std::borrow::Cow::Owned(resolved.replace('.', "_dot_"))
                } else {
                    std::borrow::Cow::Borrowed(resolved.as_str())
                };
                let func_id = if let Some(&existing) = ctx.func_ids.get(resolved.as_ref()) {
                    Ok(existing)
                } else {
                    let call_conv = platform_call_conv();
                    let mut sig = Signature::new(call_conv);
                    // receiver + args: all i64
                    for _ in 0..args.len() + 1 {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.returns.push(AbiParam::new(types::I64));
                    let result = ctx.module.declare_function(&resolved, Linkage::Import, &sig);
                    // Cache for future lookups
                    if let Ok(id) = &result {
                        ctx.func_ids.insert(resolved.to_string(), *id);
                    }
                    result
                };
                match func_id {
                    Ok(fid) => {
                        let fref = ctx.module.declare_func_in_func(fid, builder.func);
                        let mut call_args = vec![receiver_val];
                        for a in args {
                            call_args.push(get_vreg_or_default(ctx, builder, a));
                        }
                        let call_args = super::calls::adapt_args_to_signature(builder, fref, call_args);
                        let call = adapted_call(builder, fref, &call_args);
                        Some(builder.inst_results(call)[0])
                    }
                    Err(_) => {
                        // declare_function failed, fall through to rt_method_not_found
                        None
                    }
                }
            } else {
                None
            }
            .or_else(|| {
                // Fallback: call rt_method_not_found
                let type_bytes = receiver_type.as_bytes();
                let type_data_id = declare_named_bytes(ctx, type_bytes).ok()?;
                let type_global = ctx.module.declare_data_in_func(type_data_id, builder.func);
                let type_ptr = builder.ins().global_value(types::I64, type_global);
                let type_len = builder.ins().iconst(types::I64, type_bytes.len() as i64);

                let method_bytes = method.as_bytes();
                let method_data_id = declare_named_bytes(ctx, method_bytes).ok()?;
                let method_global = ctx.module.declare_data_in_func(method_data_id, builder.func);
                let method_ptr = builder.ins().global_value(types::I64, method_global);
                let method_len = builder.ins().iconst(types::I64, method_bytes.len() as i64);

                let not_found_id = ctx.runtime_funcs["rt_method_not_found"];
                let not_found_ref = ctx.module.declare_func_in_func(not_found_id, builder.func);
                let call = adapted_call(builder, not_found_ref, &[type_ptr, type_len, method_ptr, method_len]);
                Some(builder.inst_results(call)[0])
            })
        }
    };

    if let Some(d) = dest {
        let val = result.unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
        ctx.vreg_values.insert(*d, val);
    }
    Ok(())
}
