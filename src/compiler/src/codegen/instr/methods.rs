// Builtin method compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use super::{InstrContext, InstrResult};

/// Helper to call a runtime function and get its result
fn call_runtime_1<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    arg: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[arg]);
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
    let call = builder.ins().call(func_ref, &[arg1, arg2]);
    builder.inst_results(call)[0]
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
    let call = builder.ins().call(func_ref, &[arg1, arg2, arg3]);
    builder.inst_results(call)[0]
}

/// Wrap a value with rt_value_int
fn wrap_value<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    call_runtime_1(ctx, builder, "rt_value_int", val)
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
        let call = builder.ins().call(len_ref, &[receiver]);
        builder.inst_results(call)[0]
    } else {
        builder.ins().iconst(types::I64, 0)
    }
}

fn compile_builtin_method<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    receiver_type: &str,
    method: &str,
    args: &[VReg],
) -> InstrResult<()> {
    let receiver_val = ctx.vreg_values[&receiver];
    let result = match (receiver_type, method) {
        ("Array", "push") | ("array", "push") => {
            let arg_val = ctx.vreg_values[&args[0]];
            let wrapped = wrap_value(ctx, builder, arg_val);
            let result_i8 = call_runtime_2(ctx, builder, "rt_array_push", receiver_val, wrapped);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Array", "len") | ("array", "len") => {
            Some(call_len_method(ctx, builder, "rt_array_len", receiver_val))
        }
        ("Array", "get") | ("array", "get") => {
            let idx_val = ctx.vreg_values[&args[0]];
            let wrapped_idx = wrap_value(ctx, builder, idx_val);
            Some(call_runtime_2(ctx, builder, "rt_index_get", receiver_val, wrapped_idx))
        }
        ("Array", "set") | ("array", "set") => {
            let idx_val = ctx.vreg_values[&args[0]];
            let arg_val = ctx.vreg_values[&args[1]];
            let wrapped_idx = wrap_value(ctx, builder, idx_val);
            let wrapped_val = wrap_value(ctx, builder, arg_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_index_set", receiver_val, wrapped_idx, wrapped_val);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Array", "pop") | ("array", "pop") => {
            Some(call_runtime_1(ctx, builder, "rt_array_pop", receiver_val))
        }
        ("Array", "clear") | ("array", "clear") => {
            let result_i8 = call_runtime_1(ctx, builder, "rt_array_clear", receiver_val);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("String", "len") | ("string", "len") => {
            Some(call_len_method(ctx, builder, "rt_string_len", receiver_val))
        }
        ("String", "concat") | ("string", "concat") => {
            let arg_val = ctx.vreg_values[&args[0]];
            Some(call_runtime_2(ctx, builder, "rt_string_concat", receiver_val, arg_val))
        }
        ("Dict", "get") | ("dict", "get") => {
            let key_val = ctx.vreg_values[&args[0]];
            let wrapped_key = wrap_value(ctx, builder, key_val);
            Some(call_runtime_2(ctx, builder, "rt_index_get", receiver_val, wrapped_key))
        }
        ("Dict", "set") | ("dict", "set") => {
            let key_val = ctx.vreg_values[&args[0]];
            let val_val = ctx.vreg_values[&args[1]];
            let wrapped_key = wrap_value(ctx, builder, key_val);
            let wrapped_val = wrap_value(ctx, builder, val_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_dict_set", receiver_val, wrapped_key, wrapped_val);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Dict", "len") | ("dict", "len") => {
            Some(call_len_method(ctx, builder, "rt_dict_len", receiver_val))
        }
        ("Dict", "clear") | ("dict", "clear") => {
            let result_i8 = call_runtime_1(ctx, builder, "rt_dict_clear", receiver_val);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Dict", "keys") | ("dict", "keys") => {
            Some(call_runtime_1(ctx, builder, "rt_dict_keys", receiver_val))
        }
        ("Dict", "values") | ("dict", "values") => {
            Some(call_runtime_1(ctx, builder, "rt_dict_values", receiver_val))
        }
        ("Tuple", "get") | ("tuple", "get") => {
            let idx_val = ctx.vreg_values[&args[0]];
            Some(call_runtime_2(ctx, builder, "rt_tuple_get", receiver_val, idx_val))
        }
        ("Tuple", "len") | ("tuple", "len") => {
            Some(call_len_method(ctx, builder, "rt_tuple_len", receiver_val))
        }
        ("Tuple", "set") | ("tuple", "set") => {
            let idx_val = ctx.vreg_values[&args[0]];
            let arg_val = ctx.vreg_values[&args[1]];
            let wrapped = wrap_value(ctx, builder, arg_val);
            let result_i8 = call_runtime_3(ctx, builder, "rt_tuple_set", receiver_val, idx_val, wrapped);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Array", "contains") | ("array", "contains") |
        ("Dict", "contains") | ("dict", "contains") |
        ("String", "contains") | ("string", "contains") => {
            let arg_val = ctx.vreg_values[&args[0]];
            let result_i8 = call_runtime_2(ctx, builder, "rt_contains", receiver_val, arg_val);
            Some(builder.ins().uextend(types::I64, result_i8))
        }
        ("Array", "slice") | ("array", "slice") |
        ("String", "slice") | ("string", "slice") => {
            let slice_id = ctx.runtime_funcs["rt_slice"];
            let slice_ref = ctx.module.declare_func_in_func(slice_id, builder.func);
            let start = ctx.vreg_values[&args[0]];
            let end = if args.len() > 1 {
                ctx.vreg_values[&args[1]]
            } else {
                builder.ins().iconst(types::I64, i64::MAX)
            };
            let step = if args.len() > 2 {
                ctx.vreg_values[&args[2]]
            } else {
                builder.ins().iconst(types::I64, 1)
            };
            let call = builder.ins().call(slice_ref, &[receiver_val, start, end, step]);
            Some(builder.inst_results(call)[0])
        }
        _ => {
            // Unknown method - call rt_method_not_found
            let type_bytes = receiver_type.as_bytes();
            let type_data_id = ctx.module
                .declare_anonymous_data(true, false)
                .map_err(|e| e.to_string())?;
            let mut type_data_desc = cranelift_module::DataDescription::new();
            type_data_desc.define(type_bytes.to_vec().into_boxed_slice());
            ctx.module.define_data(type_data_id, &type_data_desc).map_err(|e| e.to_string())?;

            let type_global = ctx.module.declare_data_in_func(type_data_id, builder.func);
            let type_ptr = builder.ins().global_value(types::I64, type_global);
            let type_len = builder.ins().iconst(types::I64, type_bytes.len() as i64);

            let method_bytes = method.as_bytes();
            let method_data_id = ctx.module
                .declare_anonymous_data(true, false)
                .map_err(|e| e.to_string())?;
            let mut method_data_desc = cranelift_module::DataDescription::new();
            method_data_desc.define(method_bytes.to_vec().into_boxed_slice());
            ctx.module.define_data(method_data_id, &method_data_desc).map_err(|e| e.to_string())?;

            let method_global = ctx.module.declare_data_in_func(method_data_id, builder.func);
            let method_ptr = builder.ins().global_value(types::I64, method_global);
            let method_len = builder.ins().iconst(types::I64, method_bytes.len() as i64);

            let not_found_id = ctx.runtime_funcs["rt_method_not_found"];
            let not_found_ref = ctx.module.declare_func_in_func(not_found_id, builder.func);
            let call = builder.ins().call(not_found_ref, &[type_ptr, type_len, method_ptr, method_len]);
            Some(builder.inst_results(call)[0])
        }
    };

    if let Some(d) = dest {
        let val = result.unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
        ctx.vreg_values.insert(*d, val);
    }
    Ok(())
}
