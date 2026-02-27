// Closure and struct initialization helpers.

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::types_util::type_id_to_cranelift;
use super::helpers::{adapted_call, create_string_constant, get_vreg_or_default, indirect_call_with_result};
use super::{InstrContext, InstrResult};

pub(crate) fn compile_closure_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    func_name: &str,
    closure_size: usize,
    capture_offsets: &[u32],
    captures: &[VReg],
) {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);

    let size_val = builder.ins().iconst(types::I64, closure_size as i64);
    let call = adapted_call(builder, alloc_ref, &[size_val]);
    let closure_ptr = builder.inst_results(call)[0];

    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let fn_addr = builder.ins().func_addr(types::I64, func_ref);
        builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
    } else {
        let null = builder.ins().iconst(types::I64, 0);
        builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
    }

    for (i, offset) in capture_offsets.iter().enumerate() {
        let cap_val = get_vreg_or_default(ctx, builder, &captures[i]);
        builder
            .ins()
            .store(MemFlags::new(), cap_val, closure_ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, closure_ptr);
}

pub(crate) fn compile_indirect_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    callee: VReg,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let closure_ptr = get_vreg_or_default(ctx, builder, &callee);
    let fn_ptr = builder.ins().load(types::I64, MemFlags::new(), closure_ptr, 0);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![closure_ptr];
    for arg in args {
        call_args.push(get_vreg_or_default(ctx, builder, arg));
    }

    indirect_call_with_result(ctx, builder, sig_ref, fn_ptr, &call_args, dest);
}

pub(crate) fn compile_struct_init<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    struct_size: usize,
    field_offsets: &[u32],
    field_types: &[TypeId],
    field_values: &[VReg],
) {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);

    let size_val = builder.ins().iconst(types::I64, struct_size as i64);
    let call = adapted_call(builder, alloc_ref, &[size_val]);
    let ptr = builder.inst_results(call)[0];

    for (i, (offset, field_type)) in field_offsets.iter().zip(field_types.iter()).enumerate() {
        // Handle case where field_values has fewer elements than field_offsets/types
        let field_val = if i < field_values.len() {
            if let Some(&val) = ctx.vreg_values.get(&field_values[i]) {
                val
            } else {
                // VReg not found - use default value (0 for pointers/integers)
                builder.ins().iconst(types::I64, 0)
            }
        } else {
            // More fields than values - use default 0
            builder.ins().iconst(types::I64, 0)
        };
        let _cranelift_ty = type_id_to_cranelift(*field_type);
        builder.ins().store(MemFlags::new(), field_val, ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, ptr);
}

pub(crate) fn compile_method_call_static<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    func_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    // First check if this is a builtin method (String, Array methods)
    // Try to compile as builtin - these have runtime function implementations
    if let Some(result) = try_compile_builtin_method_call(ctx, builder, receiver, func_name, args)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
        return Ok(());
    }

    // Try to find the function - check multiple patterns
    // 1. Exact match (func_name)
    // 2. Type-qualified name (ClassName.method) - search for functions ending with ".func_name"
    let func_id = ctx.func_ids.get(func_name).copied().or_else(|| {
        // Search for a function ending with ".func_name" (e.g., "ArgParser.parse")
        let suffix = format!(".{}", func_name);
        ctx.func_ids.iter().find(|(k, _)| k.ends_with(&suffix)).map(|(_, &v)| v)
    });

    if let Some(func_id) = func_id {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let mut call_args = vec![get_vreg_or_default(ctx, builder, &receiver)];
        for arg in args {
            call_args.push(get_vreg_or_default(ctx, builder, arg));
        }
        let call_args = super::calls::adapt_args_to_signature(builder, func_ref, call_args);
        let call = adapted_call(builder, func_ref, &call_args);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            } else {
                let null = builder.ins().iconst(types::I64, 0);
                ctx.vreg_values.insert(*d, null);
            }
        }
    } else {
        let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

        let not_found_id = ctx.runtime_funcs["rt_function_not_found"];
        let not_found_ref = ctx.module.declare_func_in_func(not_found_id, builder.func);
        let call = adapted_call(builder, not_found_ref, &[name_ptr, name_len]);

        if let Some(d) = dest {
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*d, result);
        }
    }
    Ok(())
}

/// Try to compile a builtin method call (String, Array methods)
/// Returns Some(result_value) if the method was handled, None otherwise
fn try_compile_builtin_method_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    receiver: VReg,
    method: &str,
    args: &[VReg],
) -> InstrResult<Option<cranelift_codegen::ir::Value>> {
    let receiver_val = get_vreg_or_default(ctx, builder, &receiver);

    // Extract plain method name from qualified name (e.g., "text.len" -> "len")
    let method = method.rsplit('.').next().unwrap_or(method);

    // Handle slice specially since it has optional parameters
    if method == "slice" || method == "substring" {
        let Some(&slice_id) = ctx.runtime_funcs.get("rt_slice") else {
            return Ok(None);
        };
        let slice_ref = ctx.module.declare_func_in_func(slice_id, builder.func);

        // start argument (required)
        let start = if !args.is_empty() {
            get_vreg_or_default(ctx, builder, &args[0])
        } else {
            builder.ins().iconst(types::I64, 0)
        };

        // end argument (optional, defaults to collection length)
        let end = if args.len() > 1 {
            get_vreg_or_default(ctx, builder, &args[1])
        } else {
            // Default to collection length
            if let Some(&len_id) = ctx.runtime_funcs.get("rt_len") {
                let len_ref = ctx.module.declare_func_in_func(len_id, builder.func);
                let len_call = adapted_call(builder, len_ref, &[receiver_val]);
                builder.inst_results(len_call)[0]
            } else {
                builder.ins().iconst(types::I64, i64::MAX)
            }
        };

        // step argument (optional, defaults to 1)
        let step = if args.len() > 2 {
            get_vreg_or_default(ctx, builder, &args[2])
        } else {
            builder.ins().iconst(types::I64, 1)
        };

        let call = adapted_call(builder, slice_ref, &[receiver_val, start, end, step]);
        return Ok(Some(builder.inst_results(call)[0]));
    }

    // is_empty: compile as rt_len(receiver) == 0
    if method == "is_empty" {
        if let Some(&len_id) = ctx.runtime_funcs.get("rt_len") {
            let len_ref = ctx.module.declare_func_in_func(len_id, builder.func);
            let call = adapted_call(builder, len_ref, &[receiver_val]);
            let len_val = builder.inst_results(call)[0];
            let zero = builder.ins().iconst(types::I64, 0);
            let result = builder
                .ins()
                .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, len_val, zero);
            return Ok(Some(result));
        }
    }

    // Map method names to runtime functions
    let runtime_func = match method {
        // String methods
        "starts_with" => "rt_string_starts_with",
        "ends_with" => "rt_string_ends_with",
        "concat" => "rt_string_concat",
        "contains" => "rt_contains",
        "char_at" | "at" => "rt_string_char_at",
        // Array methods
        "push" => "rt_array_push",
        "pop" => "rt_array_pop",
        "clear" => "rt_array_clear",
        // Generic collection methods (work on String, Array, Tuple, Dict)
        "len" => "rt_len",
        // Result/Option methods
        "unwrap" | "unwrap_or" => "rt_enum_payload",
        "is_none" => {
            let Some(&func_id) = ctx.runtime_funcs.get("rt_is_none") else {
                return Ok(None);
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        "is_some" => {
            let Some(&func_id) = ctx.runtime_funcs.get("rt_is_some") else {
                return Ok(None);
            };
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let call = adapted_call(builder, func_ref, &[receiver_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        "is_ok" | "is_err" => {
            let check_variant = if method == "is_ok" { "Ok" } else { "Err" };
            let disc = {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                check_variant.hash(&mut hasher);
                (hasher.finish() & 0xFFFFFFFF) as i64
            };
            let Some(&check_id) = ctx.runtime_funcs.get("rt_enum_check_discriminant") else {
                return Ok(None);
            };
            let check_ref = ctx.module.declare_func_in_func(check_id, builder.func);
            let disc_val = builder.ins().iconst(types::I64, disc);
            let call = adapted_call(builder, check_ref, &[receiver_val, disc_val]);
            let bool_result = builder.inst_results(call)[0];
            let result = builder.ins().sextend(types::I64, bool_result);
            return Ok(Some(result));
        }
        // Map/filter/join
        "join" => "rt_string_join",
        "map" => {
            // Use rt_option_map for Option.map (also works for arrays since
            // rt_option_map checks if the value is an enum with Some/None)
            if let Some(&func_id) = ctx.runtime_funcs.get("rt_option_map") {
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                let closure_val = get_vreg_or_default(ctx, builder, &args[0]);
                let call = adapted_call(builder, func_ref, &[receiver_val, closure_val]);
                return Ok(Some(builder.inst_results(call)[0]));
            }
            return Ok(None);
        }
        "filter" => "rt_array_filter",
        "sort" => "rt_array_sort",
        "reverse" => "rt_array_reverse",
        "first" => "rt_array_first",
        "last" => "rt_array_last",
        "find" => "rt_array_find",
        "any" => "rt_array_any",
        "all" => "rt_array_all",
        // String extra methods
        "trim" => "rt_string_trim",
        "split" => "rt_string_split",
        "replace" => "rt_string_replace",
        "to_upper" | "upper" => "rt_string_to_upper",
        "to_lower" | "lower" => "rt_string_to_lower",
        "to_int" | "to_i64" | "parse_int" => "rt_string_to_int",
        "to_string" | "str" => "rt_to_string",
        // Dict/collection methods
        "get" => "rt_index_get",
        "set" => {
            if args.len() >= 2 {
                let key_val = get_vreg_or_default(ctx, builder, &args[0]);
                let val_val = get_vreg_or_default(ctx, builder, &args[1]);
                if let Some(&func_id) = ctx.runtime_funcs.get("rt_dict_set") {
                    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    let call = adapted_call(builder, func_ref, &[receiver_val, key_val, val_val]);
                    let result = builder.inst_results(call)[0];
                    return Ok(Some(super::helpers::safe_extend_to_i64(builder, result)));
                }
            }
            return Ok(None);
        }
        "keys" => "rt_dict_keys",
        "values" => "rt_dict_values",
        "contains_key" | "has_key" => "rt_contains",
        _ => return Ok(None),
    };

    // Check if runtime function exists
    let Some(&func_id) = ctx.runtime_funcs.get(runtime_func) else {
        return Ok(None);
    };

    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

    // Build call arguments: receiver first, then other args
    let mut call_args = vec![receiver_val];
    for arg in args {
        call_args.push(get_vreg_or_default(ctx, builder, arg));
    }

    let call = adapted_call(builder, func_ref, &call_args);
    let results = builder.inst_results(call);

    // Methods that mutate in-place (push, clear, reverse, sort) should return the receiver
    // so that chaining like `self.items = self.items.push(x)` works correctly.
    let in_place_mutating = matches!(
        runtime_func,
        "rt_array_push" | "rt_array_clear" | "rt_array_reverse" | "rt_array_sort"
    );

    if in_place_mutating {
        Ok(Some(receiver_val))
    } else if results.is_empty() {
        Ok(Some(builder.ins().iconst(types::I64, 0)))
    } else {
        let result = results[0];
        // Extend smaller return types (e.g., I8 from rt_contains) to I64
        let result_type = builder.func.dfg.value_type(result);
        if result_type != types::I64 {
            Ok(Some(super::helpers::safe_extend_to_i64(builder, result)))
        } else {
            Ok(Some(result))
        }
    }
}

pub(crate) fn compile_method_call_virtual<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    vtable_slot: usize,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let recv_ptr = get_vreg_or_default(ctx, builder, &receiver);
    let vtable_ptr = builder.ins().load(types::I64, MemFlags::new(), recv_ptr, 0);
    let slot_offset = (vtable_slot as i32) * 8;
    let method_ptr = builder.ins().load(types::I64, MemFlags::new(), vtable_ptr, slot_offset);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![recv_ptr];
    for arg in args {
        call_args.push(get_vreg_or_default(ctx, builder, arg));
    }

    indirect_call_with_result(ctx, builder, sig_ref, method_ptr, &call_args, dest);
}
