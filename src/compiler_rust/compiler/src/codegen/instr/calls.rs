//! Function call instruction compilation.
//!
//! Handles all forms of function calls: user-defined, runtime SFFI, and built-in functions.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{Linkage, Module};

use crate::codegen::runtime_sffi::RUNTIME_FUNCS;
use crate::hir::TypeId;
use crate::mir::{CallTarget, VReg};

use super::core::{compile_builtin_io_call, vreg_is_signed};
use super::helpers::{
    adapted_call, call_runtime_1, call_runtime_2, call_runtime_3, create_cstring_constant, get_vreg_or_default,
    inline_runtime_array_len_value, inline_runtime_len_value,
};
use super::{InstrContext, InstrResult};

/// Check if a function name is a profiler function (to avoid recursive instrumentation)
/// Bitcast call args that are F32/F64 per MIR `vreg_types` but arrive as
/// Cranelift I64 (cross-block floats travel as raw f64 bits in i64) back to
/// f64 before signature adaptation. Without this, `adapt_value_to_type`'s
/// int→float arm value-converts the raw bits (`math_sqrt(dist_sq)` became
/// sqrt(4.6e18) in the physics narrowphase). Safe for i64 params too: the
/// float→i64 adaptation arm bitcasts back, round-tripping the exact bits.
fn reinterpret_float_bit_args<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    args: &[VReg],
    arg_vals: Vec<Value>,
) -> Vec<Value> {
    arg_vals
        .into_iter()
        .enumerate()
        .map(|(i, v)| {
            if args
                .get(i)
                .is_some_and(|vreg| matches!(ctx.vreg_types.get(vreg).copied(), Some(TypeId::F64) | Some(TypeId::F32)))
                && builder.func.dfg.value_type(v) == types::I64
            {
                builder.ins().bitcast(types::F64, MemFlags::new(), v)
            } else {
                v
            }
        })
        .collect()
}

fn is_profiler_function(name: &str) -> bool {
    name.starts_with("rt_profiler_")
}

fn linkage_is_defined_local(linkage: Option<Linkage>) -> bool {
    linkage.is_some_and(|linkage| linkage != Linkage::Import)
}

fn has_defined_local_function<M: Module>(ctx: &InstrContext<'_, M>, name: &str) -> bool {
    let Some(&func_id) = ctx.func_ids.get(name) else {
        return false;
    };
    linkage_is_defined_local(Some(ctx.module.declarations().get_function_decl(func_id).linkage))
}

fn compile_user_function_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    func_name: &str,
    args: &[VReg],
    callee_id: cranelift_module::FuncId,
) -> InstrResult<()> {
    if !is_profiler_function(func_name) {
        emit_profiler_call(ctx, builder, func_name)?;
    }
    let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
    let arg_vals: Vec<_> = args.iter().map(|a| get_vreg_or_default(ctx, builder, a)).collect();
    let arg_vals = reinterpret_float_bit_args(ctx, builder, args, arg_vals);
    let arg_signed: Vec<Option<bool>> = args.iter().map(|arg| super::core::vreg_is_signed(ctx, *arg)).collect();
    let arg_vals = adapt_args_to_signature_with_signedness(builder, callee_ref, arg_vals, Some(&arg_signed));
    let call = adapted_call(builder, callee_ref, &arg_vals);
    if !is_profiler_function(func_name) {
        emit_profiler_return(ctx, builder)?;
    }
    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            ctx.vreg_values.insert(*d, builder.ins().iconst(types::I64, 0));
        }
    }
    Ok(())
}

fn is_cross_module_data_export<M: Module>(ctx: &InstrContext<'_, M>, raw_name: &str, resolved_name: &str) -> bool {
    ctx.data_exports.contains(raw_name)
        || ctx.data_exports.contains(resolved_name)
        || ctx.data_exports.contains(&resolved_name.replace('.', "_dot_"))
}

fn inline_numeric_arg(builder: &mut FunctionBuilder, value: Value) -> Value {
    let zero = builder.ins().iconst(types::I64, 0);
    let eight = builder.ins().iconst(types::I64, 8);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let tag = builder.ins().band(value, tag_mask);
    let is_int_tag = builder.ins().icmp(IntCC::Equal, tag, zero);
    let is_tagged_payload = builder.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, value, eight);
    let is_tagged_int = builder.ins().band(is_int_tag, is_tagged_payload);
    let payload = builder.ins().sshr_imm(value, 3);
    builder.ins().select(is_tagged_int, payload, value)
}

/// Type-aware variant of [`inline_numeric_arg`]: a VReg whose MIR type is a
/// known scalar integer is a RAW machine integer, so skip the tagged-int
/// heuristic — it false-positives on any raw value that is a multiple of 8
/// (e.g. color 0xFF202020 written through `[u32]` set arrived as value>>3,
/// blanking the engine3d framebuffer clear).
fn inline_numeric_arg_typed<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    vreg: VReg,
    value: Value,
) -> Value {
    if vreg_is_signed(ctx, vreg).is_some() {
        return value;
    }
    inline_numeric_arg(builder, value)
}

// create_cstring_constant is now imported from helpers

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
        adapted_call(builder, record_call_ref, &adapted);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use cranelift_module::Linkage;

    use super::{linkage_is_defined_local, sffi_alias_target};

    #[test]
    fn conversion_aliases_resolve_to_runtime_symbols() {
        assert_eq!(sffi_alias_target("to_int"), Some("rt_string_to_int"));
        assert_eq!(sffi_alias_target("to_i64"), Some("rt_string_to_int"));
        assert_eq!(sffi_alias_target("parse_int"), Some("rt_string_to_int"));
        assert_eq!(sffi_alias_target("to_float"), Some("rt_string_to_float"));
        assert_eq!(sffi_alias_target("to_f64"), Some("rt_string_to_float"));
        assert_eq!(sffi_alias_target("to_string"), Some("rt_to_string"));
        assert_eq!(sffi_alias_target("to_text"), Some("rt_to_string"));
        assert_eq!(sffi_alias_target("rt_file_delete"), Some("rt_file_remove"));
        assert_eq!(sffi_alias_target("dealloc"), Some("rt_free"));
    }

    #[test]
    fn only_defined_local_functions_shadow_runtime_symbols() {
        assert!(linkage_is_defined_local(Some(Linkage::Export)));
        assert!(linkage_is_defined_local(Some(Linkage::Local)));
        assert!(!linkage_is_defined_local(Some(Linkage::Import)));
        assert!(!linkage_is_defined_local(None));
    }
}

fn emit_profiler_return<M: Module>(ctx: &mut InstrContext<'_, M>, builder: &mut FunctionBuilder) -> InstrResult<()> {
    if !crate::runtime_profile::is_profiling_active() {
        return Ok(());
    }
    if let Some(&record_return_id) = ctx.runtime_funcs.get("rt_profiler_record_return") {
        let record_return_ref = ctx.module.declare_func_in_func(record_return_id, builder.func);
        adapted_call(builder, record_return_ref, &[]);
    }
    Ok(())
}

fn compile_simple_runtime_memory_intrinsic<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    intrinsic: &str,
    args: &[VReg],
) -> InstrResult<bool> {
    if !matches!(
        intrinsic,
        "spl_load_i64" | "spl_store_i64" | "spl_load_u8" | "spl_store_u8" | "spl_f64_to_bits"
    ) {
        return Ok(false);
    }

    if intrinsic == "spl_f64_to_bits" {
        if args.len() != 1 {
            return Err(format!("{intrinsic} expects 1 args, got {}", args.len()));
        }
        let Some(d) = dest else {
            return Ok(true);
        };
        let value = get_vreg_or_default(ctx, builder, &args[0]);
        let value_ty = builder.func.dfg.value_type(value);
        let bits = if value_ty == types::F64 {
            builder.ins().bitcast(types::I64, MemFlags::new(), value)
        } else if value_ty == types::F32 {
            let promoted = builder.ins().fpromote(types::F64, value);
            builder.ins().bitcast(types::I64, MemFlags::new(), promoted)
        } else {
            value
        };
        ctx.vreg_values.insert(*d, bits);
        return Ok(true);
    }

    let expected_args = if intrinsic.starts_with("spl_load_") { 2 } else { 3 };
    if args.len() != expected_args {
        return Err(format!("{intrinsic} expects {expected_args} args, got {}", args.len()));
    }

    let base = get_vreg_or_default(ctx, builder, &args[0]);
    let offset = get_vreg_or_default(ctx, builder, &args[1]);
    let addr = builder.ins().iadd(base, offset);
    let flags = MemFlags::new();

    match intrinsic {
        "spl_load_i64" => {
            let loaded = builder.ins().load(types::I64, flags, addr, 0);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, loaded);
            }
        }
        "spl_load_u8" => {
            let loaded = builder.ins().load(types::I8, flags, addr, 0);
            let widened = builder.ins().uextend(types::I64, loaded);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, widened);
            }
        }
        "spl_store_i64" | "spl_store_u8" => {
            let value = get_vreg_or_default(ctx, builder, &args[2]);
            let value = if intrinsic == "spl_store_u8" {
                builder.ins().ireduce(types::I8, value)
            } else {
                value
            };
            builder.ins().store(flags, value, addr, 0);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, builder.ins().iconst(types::I64, 0));
            }
        }
        _ => unreachable!(),
    }

    Ok(true)
}

fn compile_inline_len<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    trusted_array: bool,
) -> InstrResult<bool> {
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let value = coerce_vreg_to_i64(ctx, builder, args[0]);
    let result = if trusted_array {
        inline_runtime_array_len_value(builder, value)
    } else {
        inline_runtime_len_value(builder, value)
    };
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn ctype_call_name<M: Module>(ctx: &InstrContext<'_, M>, func_name: &str, sffi_name: &str) -> Option<&'static str> {
    let resolved = ctx
        .use_map
        .get(func_name)
        .or_else(|| ctx.import_map.get(func_name))
        .map(|name| name.as_str())
        .unwrap_or(func_name);
    if !func_name.contains("ctype") && !resolved.contains("ctype") {
        return None;
    }
    match sffi_name {
        "digit" | "is_digit" => Some("digit"),
        "upper" | "is_upper" => Some("upper"),
        "lower" | "is_lower" => Some("lower"),
        "alpha" | "is_alpha" => Some("alpha"),
        "alnum" | "is_alnum" => Some("alnum"),
        "xdigit" | "is_xdigit" => Some("xdigit"),
        "space" | "is_space" => Some("space"),
        "to_lower" => Some("to_lower"),
        "to_upper" => Some("to_upper"),
        _ => None,
    }
}

fn inline_char_range(builder: &mut FunctionBuilder, ch: Value, lo: i64, hi: i64) -> Value {
    let shifted = builder.ins().iadd_imm(ch, -lo);
    builder.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, shifted, hi - lo)
}

pub(crate) fn compile_inline_ctype_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    func_name: &str,
    sffi_name: &str,
    args: &[VReg],
) -> InstrResult<bool> {
    let Some(kind) = ctype_call_name(ctx, func_name, sffi_name) else {
        return Ok(false);
    };
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(true);
    };

    let ch = coerce_vreg_to_i64(ctx, builder, args[0]);
    let digit = inline_char_range(builder, ch, 48, 57);
    let upper = inline_char_range(builder, ch, 65, 90);
    let lower = inline_char_range(builder, ch, 97, 122);
    let case_fold_mask = builder.ins().iconst(types::I64, 32);
    let folded = builder.ins().bor(ch, case_fold_mask);
    let alpha_folded = inline_char_range(builder, folded, 97, 122);
    let result = match kind {
        "digit" => digit,
        "upper" => upper,
        "lower" => lower,
        "alpha" => alpha_folded,
        "alnum" => builder.ins().bor(alpha_folded, digit),
        "xdigit" => {
            let hex_alpha = inline_char_range(builder, folded, 97, 102);
            builder.ins().bor(digit, hex_alpha)
        }
        "space" => {
            let sp = builder.ins().icmp_imm(IntCC::Equal, ch, 32);
            let control_space = inline_char_range(builder, ch, 9, 13);
            builder.ins().bor(sp, control_space)
        }
        "to_lower" => {
            let delta = builder.ins().iconst(types::I64, 32);
            let converted = builder.ins().iadd(ch, delta);
            builder.ins().select(upper, converted, ch)
        }
        "to_upper" => {
            let delta = builder.ins().iconst(types::I64, 32);
            let converted = builder.ins().isub(ch, delta);
            builder.ins().select(lower, converted, ch)
        }
        _ => return Ok(false),
    };
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_bytes_u8_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    trusted_array: bool,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let byte_mask = builder.ins().iconst(types::I64, 0xff);
    let index_is_unsigned = matches!(
        ctx.vreg_types.get(&args[1]).copied(),
        Some(TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64)
    );

    let bounds_block = builder.create_block();
    let load_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let ptr_bits = builder.ins().band(array, ptr_mask);
    if trusted_array {
        builder.ins().jump(bounds_block, &[]);
    } else {
        let type_block = builder.create_block();
        let tag = builder.ins().band(array, tag_mask);
        let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
        builder.ins().brif(is_heap, type_block, &[], done_block, &[zero]);

        builder.switch_to_block(type_block);
        let object_type = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 0);
        let is_array = builder.ins().icmp_imm(IntCC::Equal, object_type, 2);
        builder.ins().brif(is_array, bounds_block, &[], done_block, &[zero]);
        builder.seal_block(type_block);
    }

    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let (normalized_index, in_bounds) = if index_is_unsigned {
        let lt_len = builder.ins().icmp(IntCC::UnsignedLessThan, index, len);
        (index, lt_len)
    } else {
        let index_is_negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let negative_index = builder.ins().iadd(len, index);
        let normalized_index = builder.ins().select(index_is_negative, negative_index, index);
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        let in_bounds = builder.ins().band(ge_zero, lt_len);
        (normalized_index, in_bounds)
    };
    builder.ins().brif(in_bounds, load_block, &[], done_block, &[zero]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(load_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let packed_block = builder.create_block();
    let slot_block = builder.create_block();
    let gc_flags = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 1);
    let byte_packed = builder.ins().band_imm(gc_flags, 8);
    let is_byte_packed = builder.ins().icmp_imm(IntCC::NotEqual, byte_packed, 0);
    builder.ins().brif(is_byte_packed, packed_block, &[], slot_block, &[]);
    builder.seal_block(load_block);

    builder.switch_to_block(packed_block);
    let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
    let packed_byte = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
    let packed_value = builder.ins().uextend(types::I64, packed_byte);
    builder.ins().jump(done_block, &[packed_value]);
    builder.seal_block(packed_block);

    builder.switch_to_block(slot_block);
    let slot_offset = builder.ins().imul_imm(normalized_index, 8);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    let raw_tag = builder.ins().band(raw, tag_mask);
    let raw_is_int = builder.ins().icmp(IntCC::Equal, raw_tag, zero);
    let int_payload = builder.ins().sshr_imm(raw, 3);
    let int_byte = builder.ins().band(int_payload, byte_mask);
    let raw_byte = builder.ins().band(raw, byte_mask);
    let value = builder.ins().select(raw_is_int, int_byte, raw_byte);
    builder.ins().jump(done_block, &[value]);
    builder.seal_block(slot_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_bytes_le_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);

    let load_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let ge_zero = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, index, zero);
    let end = builder.ins().iadd_imm(index, width);
    let in_len = builder.ins().icmp(IntCC::SignedLessThanOrEqual, end, len);
    let in_bounds = builder.ins().band(ge_zero, in_len);
    builder.ins().brif(in_bounds, load_block, &[], done_block, &[zero]);

    builder.switch_to_block(load_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let byte_ptr = builder.ins().iadd(data_ptr, index);
    let loaded = if width == 8 {
        builder.ins().load(types::I64, MemFlags::new(), byte_ptr, 0)
    } else if width == 1 {
        let value = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
        builder.ins().uextend(types::I64, value)
    } else {
        let value = builder.ins().load(types::I32, MemFlags::new(), byte_ptr, 0);
        builder.ins().uextend(types::I64, value)
    };
    builder.ins().jump(done_block, &[loaded]);
    builder.seal_block(load_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_typed_bytes_le_unchecked<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let byte_ptr = builder.ins().iadd(data_ptr, index);
    let loaded = if width == 8 {
        builder.ins().load(types::I64, MemFlags::new(), byte_ptr, 0)
    } else if width == 1 {
        let value = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
        builder.ins().uextend(types::I64, value)
    } else {
        let value = builder.ins().load(types::I32, MemFlags::new(), byte_ptr, 0);
        builder.ins().uextend(types::I64, value)
    };
    ctx.vreg_values.insert(*dest, loaded);
    Ok(true)
}

fn compile_inline_array_data_ptr<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };
    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    ctx.vreg_values.insert(*dest, data_ptr);
    Ok(true)
}

fn compile_inline_array_header_ptr<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };
    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    ctx.vreg_values.insert(*dest, ptr_bits);
    Ok(true)
}

fn compile_inline_array_get<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let nil = builder.ins().iconst(types::I64, 3);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);

    // Blocks: nil_check → bounds_block → load_block → {byte_block, word_block} → done_block
    let bounds_block = builder.create_block();
    let load_block = builder.create_block();
    let byte_block = builder.create_block();
    let word_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    // Guard: array must be a heap pointer (tag == 1). Nil (tag==3) or integer would
    // load from address 0 if we skipped this, causing SIGSEGV.
    let tag = builder.ins().band(array, tag_mask);
    let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
    builder.ins().brif(is_heap, bounds_block, &[], done_block, &[nil]);

    // Bounds check — len and normalized_index computed here, after we know ptr is valid.
    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };
    let in_bounds = if index_is_unsigned {
        builder.ins().icmp(IntCC::UnsignedLessThan, normalized_index, len)
    } else {
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        builder.ins().band(ge_zero, lt_len)
    };
    builder.ins().brif(in_bounds, load_block, &[], done_block, &[nil]);
    builder.seal_block(bounds_block);

    // Load data_ptr only after bounds check passes — avoids the wild read on OOB.
    builder.switch_to_block(load_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let flags = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 1);
    let flags64 = builder.ins().uextend(types::I64, flags);
    let byte_packed = builder.ins().band_imm(flags64, 0x08);
    let is_byte_packed = builder.ins().icmp_imm(IntCC::NotEqual, byte_packed, 0);
    builder.ins().brif(is_byte_packed, byte_block, &[], word_block, &[]);
    builder.seal_block(load_block);

    builder.switch_to_block(byte_block);
    let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
    let byte = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
    let byte_value = builder.ins().uextend(types::I64, byte);
    builder.ins().jump(done_block, &[byte_value]);
    builder.seal_block(byte_block);

    builder.switch_to_block(word_block);
    let slot_offset = builder.ins().ishl_imm(normalized_index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let value = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    builder.ins().jump(done_block, &[value]);
    builder.seal_block(word_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_array_get_word<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let nil = builder.ins().iconst(types::I64, 3);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);

    let bounds_block = builder.create_block();
    let load_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    // Guard: must be heap pointer (tag == 1) before dereferencing.
    let tag = builder.ins().band(array, tag_mask);
    let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
    builder.ins().brif(is_heap, bounds_block, &[], done_block, &[nil]);

    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };
    let in_bounds = if index_is_unsigned {
        builder.ins().icmp(IntCC::UnsignedLessThan, normalized_index, len)
    } else {
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        builder.ins().band(ge_zero, lt_len)
    };
    builder.ins().brif(in_bounds, load_block, &[], done_block, &[nil]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(load_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().ishl_imm(normalized_index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let value = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    builder.ins().jump(done_block, &[value]);
    builder.seal_block(load_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_array_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let value = get_vreg_or_default(ctx, builder, &args[2]);
    let zero = builder.ins().iconst(types::I64, 0);
    let one = builder.ins().iconst(types::I64, 1);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);

    let bounds_block = builder.create_block();
    let store_block = builder.create_block();
    let byte_block = builder.create_block();
    let word_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    // Guard: must be heap pointer (tag == 1) before dereferencing.
    let tag = builder.ins().band(array, tag_mask);
    let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
    builder.ins().brif(is_heap, bounds_block, &[], done_block, &[zero]);

    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };
    let in_bounds = if index_is_unsigned {
        builder.ins().icmp(IntCC::UnsignedLessThan, normalized_index, len)
    } else {
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        builder.ins().band(ge_zero, lt_len)
    };
    builder.ins().brif(in_bounds, store_block, &[], done_block, &[zero]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let flags = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 1);
    let flags64 = builder.ins().uextend(types::I64, flags);
    let byte_packed = builder.ins().band_imm(flags64, 0x08);
    let is_byte_packed = builder.ins().icmp_imm(IntCC::NotEqual, byte_packed, 0);
    builder.ins().brif(is_byte_packed, byte_block, &[], word_block, &[]);
    builder.seal_block(store_block);

    builder.switch_to_block(byte_block);
    let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
    let byte_value = builder.ins().ireduce(types::I8, value);
    builder.ins().store(MemFlags::new(), byte_value, byte_ptr, 0);
    builder.ins().jump(done_block, &[one]);
    builder.seal_block(byte_block);

    builder.switch_to_block(word_block);
    let slot_offset = builder.ins().ishl_imm(normalized_index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    builder.ins().store(MemFlags::new(), value, slot_ptr, 0);
    builder.ins().jump(done_block, &[one]);
    builder.seal_block(word_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    if let Some(dest) = dest {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn compile_inline_array_set_word<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let value = get_vreg_or_default(ctx, builder, &args[2]);
    let zero = builder.ins().iconst(types::I64, 0);
    let one = builder.ins().iconst(types::I64, 1);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);

    let bounds_block = builder.create_block();
    let store_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    // Guard: must be heap pointer (tag == 1) before dereferencing.
    let tag = builder.ins().band(array, tag_mask);
    let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
    builder.ins().brif(is_heap, bounds_block, &[], done_block, &[zero]);

    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };
    let in_bounds = if index_is_unsigned {
        builder.ins().icmp(IntCC::UnsignedLessThan, normalized_index, len)
    } else {
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        builder.ins().band(ge_zero, lt_len)
    };
    builder.ins().brif(in_bounds, store_block, &[], done_block, &[zero]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().ishl_imm(normalized_index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    builder.ins().store(MemFlags::new(), value, slot_ptr, 0);
    builder.ins().jump(done_block, &[one]);
    builder.seal_block(store_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    if let Some(dest) = dest {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn compile_inline_numeric_xor_sum_u64<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    raw_data: bool,
) -> InstrResult<bool> {
    let expected_args = if raw_data { 3 } else { 2 };
    if args.len() != expected_args {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let first_arg = coerce_vreg_to_i64(ctx, builder, args[0]);
    let length_arg = if raw_data {
        Some(coerce_vreg_to_i64(ctx, builder, args[1]))
    } else {
        None
    };
    let xor_value = coerce_vreg_to_i64(ctx, builder, args[if raw_data { 2 } else { 1 }]);
    let zero = builder.ins().iconst(types::I64, 0);
    let min_heap_value = builder.ins().iconst(types::I64, 4096);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = if raw_data {
        first_arg
    } else {
        builder.ins().band(first_arg, ptr_mask)
    };

    let kind_block = builder.create_block();
    let len_block = builder.create_block();
    let loop_block = builder.create_block();
    let chunk_block = builder.create_block();
    let chunk_second_block = builder.create_block();
    let tail_block = builder.create_block();
    let tail_scalar_block = builder.create_block();
    let tail_body_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(loop_block, types::I64X2);
    builder.append_block_param(loop_block, types::I64X2);
    builder.append_block_param(loop_block, types::I64X2);
    builder.append_block_param(loop_block, types::I64X2);
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(chunk_second_block, types::I64X2);
    builder.append_block_param(chunk_second_block, types::I64X2);
    builder.append_block_param(chunk_second_block, types::I64X2);
    builder.append_block_param(chunk_second_block, types::I64X2);
    builder.append_block_param(chunk_second_block, types::I64);
    builder.append_block_param(chunk_second_block, types::I64);
    builder.append_block_param(tail_block, types::I64X2);
    builder.append_block_param(tail_block, types::I64X2);
    builder.append_block_param(tail_block, types::I64X2);
    builder.append_block_param(tail_block, types::I64X2);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(tail_scalar_block, types::I64);
    builder.append_block_param(tail_scalar_block, types::I64);
    builder.append_block_param(tail_scalar_block, types::I64);
    builder.append_block_param(done_block, types::I64);

    let xor_vec = builder.ins().splat(types::I64X2, xor_value);

    if raw_data {
        let length = length_arg.expect("raw numeric xor-sum lowering provides length");
        let negative_len = builder.ins().icmp(IntCC::SignedLessThan, length, zero);
        let zero_vec = builder.ins().splat(types::I64X2, zero);
        builder.ins().brif(
            negative_len,
            done_block,
            &[zero],
            loop_block,
            &[zero_vec, zero_vec, zero_vec, zero_vec, zero, ptr_bits],
        );
    } else {
        let too_small = builder.ins().icmp(IntCC::SignedLessThan, first_arg, min_heap_value);
        builder.ins().brif(too_small, done_block, &[zero], kind_block, &[]);

        builder.switch_to_block(kind_block);
        let tag = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 0);
        let tag64 = builder.ins().uextend(types::I64, tag);
        let is_array = builder.ins().icmp_imm(IntCC::Equal, tag64, 2);
        builder.ins().brif(is_array, len_block, &[], done_block, &[zero]);
        builder.seal_block(kind_block);

        builder.switch_to_block(len_block);
        let length = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
        let negative_len = builder.ins().icmp(IntCC::SignedLessThan, length, zero);
        let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
        let zero_vec = builder.ins().splat(types::I64X2, zero);
        builder.ins().brif(
            negative_len,
            done_block,
            &[zero],
            loop_block,
            &[zero_vec, zero_vec, zero_vec, zero_vec, zero, data_ptr],
        );
        builder.seal_block(len_block);
    }

    builder.switch_to_block(loop_block);
    let sum0 = builder.block_params(loop_block)[0];
    let sum1 = builder.block_params(loop_block)[1];
    let sum2 = builder.block_params(loop_block)[2];
    let sum3 = builder.block_params(loop_block)[3];
    let idx = builder.block_params(loop_block)[4];
    let cursor = builder.block_params(loop_block)[5];
    let length = if raw_data {
        length_arg.expect("raw numeric xor-sum lowering provides length")
    } else {
        builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8)
    };
    let idx_plus_fifteen = builder.ins().iadd_imm(idx, 15);
    let has_chunk = builder.ins().icmp(IntCC::SignedLessThan, idx_plus_fifteen, length);
    builder.ins().brif(
        has_chunk,
        chunk_block,
        &[],
        tail_block,
        &[sum0, sum1, sum2, sum3, idx, cursor],
    );

    builder.switch_to_block(chunk_block);
    let value0 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 0);
    let value1 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 16);
    let value2 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 32);
    let value3 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 48);
    let xored0 = builder.ins().bxor(value0, xor_vec);
    let xored1 = builder.ins().bxor(value1, xor_vec);
    let xored2 = builder.ins().bxor(value2, xor_vec);
    let xored3 = builder.ins().bxor(value3, xor_vec);
    let next_sum0 = builder.ins().iadd(sum0, xored0);
    let next_sum1 = builder.ins().iadd(sum1, xored1);
    let next_sum2 = builder.ins().iadd(sum2, xored2);
    let next_sum3 = builder.ins().iadd(sum3, xored3);
    let next_idx = builder.ins().iadd_imm(idx, 8);
    let next_cursor = builder.ins().iadd_imm(cursor, 64);
    builder.ins().jump(
        chunk_second_block,
        &[next_sum0, next_sum1, next_sum2, next_sum3, next_idx, next_cursor],
    );
    builder.seal_block(chunk_block);

    builder.switch_to_block(chunk_second_block);
    let sum0 = builder.block_params(chunk_second_block)[0];
    let sum1 = builder.block_params(chunk_second_block)[1];
    let sum2 = builder.block_params(chunk_second_block)[2];
    let sum3 = builder.block_params(chunk_second_block)[3];
    let idx = builder.block_params(chunk_second_block)[4];
    let cursor = builder.block_params(chunk_second_block)[5];
    let value0 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 0);
    let value1 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 16);
    let value2 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 32);
    let value3 = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 48);
    let xored0 = builder.ins().bxor(value0, xor_vec);
    let xored1 = builder.ins().bxor(value1, xor_vec);
    let xored2 = builder.ins().bxor(value2, xor_vec);
    let xored3 = builder.ins().bxor(value3, xor_vec);
    let next_sum0 = builder.ins().iadd(sum0, xored0);
    let next_sum1 = builder.ins().iadd(sum1, xored1);
    let next_sum2 = builder.ins().iadd(sum2, xored2);
    let next_sum3 = builder.ins().iadd(sum3, xored3);
    let next_idx = builder.ins().iadd_imm(idx, 8);
    let next_cursor = builder.ins().iadd_imm(cursor, 64);
    builder.ins().jump(
        loop_block,
        &[next_sum0, next_sum1, next_sum2, next_sum3, next_idx, next_cursor],
    );
    builder.seal_block(chunk_second_block);
    builder.seal_block(loop_block);

    builder.switch_to_block(tail_block);
    let tail_sum_vec0 = builder.block_params(tail_block)[0];
    let tail_sum_vec1 = builder.block_params(tail_block)[1];
    let tail_sum_vec2 = builder.block_params(tail_block)[2];
    let tail_sum_vec3 = builder.block_params(tail_block)[3];
    let tail_idx = builder.block_params(tail_block)[4];
    let tail_cursor = builder.block_params(tail_block)[5];
    let has_tail = builder.ins().icmp(IntCC::SignedLessThan, tail_idx, length);
    let tail_sum_vec01 = builder.ins().iadd(tail_sum_vec0, tail_sum_vec1);
    let tail_sum_vec23 = builder.ins().iadd(tail_sum_vec2, tail_sum_vec3);
    let tail_sum_vec = builder.ins().iadd(tail_sum_vec01, tail_sum_vec23);
    let tail_sum_lo = builder.ins().extractlane(tail_sum_vec, 0);
    let tail_sum_hi = builder.ins().extractlane(tail_sum_vec, 1);
    let tail_sum = builder.ins().iadd(tail_sum_lo, tail_sum_hi);
    let result_sum = if raw_data {
        tail_sum
    } else {
        builder.ins().ishl_imm(tail_sum, 3)
    };
    builder.ins().brif(
        has_tail,
        tail_scalar_block,
        &[tail_sum, tail_idx, tail_cursor],
        done_block,
        &[result_sum],
    );

    builder.switch_to_block(tail_scalar_block);
    let tail_sum = builder.block_params(tail_scalar_block)[0];
    let tail_idx = builder.block_params(tail_scalar_block)[1];
    let tail_cursor = builder.block_params(tail_scalar_block)[2];
    let has_tail = builder.ins().icmp(IntCC::SignedLessThan, tail_idx, length);
    let result_sum = if raw_data {
        tail_sum
    } else {
        builder.ins().ishl_imm(tail_sum, 3)
    };
    builder
        .ins()
        .brif(has_tail, tail_body_block, &[], done_block, &[result_sum]);

    builder.switch_to_block(tail_body_block);
    let value = builder.ins().load(types::I64, MemFlags::new(), tail_cursor, 0);
    let xored = builder.ins().bxor(value, xor_value);
    let next_tail_sum = builder.ins().iadd(tail_sum, xored);
    let next_tail_idx = builder.ins().iadd_imm(tail_idx, 1);
    let next_tail_cursor = builder.ins().iadd_imm(tail_cursor, 8);
    builder
        .ins()
        .jump(tail_scalar_block, &[next_tail_sum, next_tail_idx, next_tail_cursor]);
    builder.seal_block(tail_body_block);
    builder.seal_block(tail_scalar_block);
    builder.seal_block(tail_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_hash_text<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let value = coerce_vreg_to_i64(ctx, builder, args[0]);
    let zero = builder.ins().iconst(types::I64, 0);
    let hash_seed = builder.ins().iconst(types::I64, 5381);
    let tag = builder.ins().band_imm(value, 7);
    let is_text = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
    let ptr = builder.ins().band_imm(value, !7i64);

    let ptr_block = builder.create_block();
    let kind_block = builder.create_block();
    let len_block = builder.create_block();
    let loop_block = builder.create_block();
    let word_block = builder.create_block();
    let tail_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(word_block, types::I64);
    builder.append_block_param(word_block, types::I64);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(done_block, types::I64);

    builder.ins().brif(is_text, ptr_block, &[], done_block, &[zero]);

    builder.switch_to_block(ptr_block);
    let ptr_valid = builder.ins().icmp_imm(IntCC::SignedGreaterThan, ptr, 0);
    builder.ins().brif(ptr_valid, kind_block, &[], done_block, &[zero]);
    builder.seal_block(ptr_block);

    builder.switch_to_block(kind_block);
    let kind = builder.ins().load(types::I64, MemFlags::new(), ptr, 0);
    let masked_kind = builder.ins().band_imm(kind, 0xFFFF_FFFF);
    let is_string = builder.ins().icmp_imm(IntCC::Equal, masked_kind, 1398034993);
    builder.ins().brif(is_string, len_block, &[], done_block, &[zero]);
    builder.seal_block(kind_block);

    builder.switch_to_block(len_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr, 8);
    let data = builder.ins().iadd_imm(ptr, 16);
    builder.ins().jump(loop_block, &[hash_seed, zero]);
    builder.seal_block(len_block);

    builder.switch_to_block(loop_block);
    let hash = builder.block_params(loop_block)[0];
    let index = builder.block_params(loop_block)[1];
    let index_plus_three = builder.ins().iadd_imm(index, 3);
    let has_word = builder.ins().icmp(IntCC::SignedLessThan, index_plus_three, len);
    builder
        .ins()
        .brif(has_word, word_block, &[hash, index], tail_block, &[hash, index]);

    builder.switch_to_block(word_block);
    let hash = builder.block_params(word_block)[0];
    let index = builder.block_params(word_block)[1];
    let byte0_ptr = builder.ins().iadd(data, index);
    let index1 = builder.ins().iadd_imm(index, 1);
    let index2 = builder.ins().iadd_imm(index, 2);
    let index3 = builder.ins().iadd_imm(index, 3);
    let byte1_ptr = builder.ins().iadd(data, index1);
    let byte2_ptr = builder.ins().iadd(data, index2);
    let byte3_ptr = builder.ins().iadd(data, index3);
    let byte0 = builder.ins().load(types::I8, MemFlags::new(), byte0_ptr, 0);
    let byte1 = builder.ins().load(types::I8, MemFlags::new(), byte1_ptr, 0);
    let byte2 = builder.ins().load(types::I8, MemFlags::new(), byte2_ptr, 0);
    let byte3 = builder.ins().load(types::I8, MemFlags::new(), byte3_ptr, 0);
    let byte0_64 = builder.ins().uextend(types::I64, byte0);
    let byte1_64 = builder.ins().uextend(types::I64, byte1);
    let byte2_64 = builder.ins().uextend(types::I64, byte2);
    let byte3_64 = builder.ins().uextend(types::I64, byte3);
    let hash_scaled = builder.ins().imul_imm(hash, 1185921);
    let term0 = builder.ins().imul_imm(byte0_64, 35937);
    let term1 = builder.ins().imul_imm(byte1_64, 1089);
    let term2 = builder.ins().imul_imm(byte2_64, 33);
    let partial0 = builder.ins().iadd(hash_scaled, term0);
    let partial1 = builder.ins().iadd(partial0, term1);
    let partial2 = builder.ins().iadd(partial1, term2);
    let next_hash = builder.ins().iadd(partial2, byte3_64);
    let next_index = builder.ins().iadd_imm(index, 4);
    let next_index_plus_three = builder.ins().iadd_imm(next_index, 3);
    let has_next_word = builder.ins().icmp(IntCC::SignedLessThan, next_index_plus_three, len);
    builder.ins().brif(
        has_next_word,
        loop_block,
        &[next_hash, next_index],
        tail_block,
        &[next_hash, next_index],
    );
    builder.seal_block(word_block);
    builder.seal_block(loop_block);

    builder.switch_to_block(tail_block);
    let hash = builder.block_params(tail_block)[0];
    let index = builder.block_params(tail_block)[1];
    let has_tail = builder.ins().icmp(IntCC::SignedLessThan, index, len);
    let tail_body_block = builder.create_block();
    builder.ins().brif(has_tail, tail_body_block, &[], done_block, &[hash]);

    builder.switch_to_block(tail_body_block);
    let byte_ptr = builder.ins().iadd(data, index);
    let byte = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
    let byte_64 = builder.ins().uextend(types::I64, byte);
    let shifted = builder.ins().ishl_imm(hash, 5);
    let hash_times_33 = builder.ins().iadd(shifted, hash);
    let next_hash = builder.ins().iadd(hash_times_33, byte_64);
    let next_index = builder.ins().iadd_imm(index, 1);
    builder.ins().jump(tail_block, &[next_hash, next_index]);
    builder.seal_block(tail_body_block);
    builder.seal_block(tail_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn vector_compare_mask_i64x2(builder: &mut FunctionBuilder, lhs: Value, rhs: Value) -> Value {
    builder.ins().icmp(IntCC::Equal, lhs, rhs)
}

fn compile_inline_numeric_contains_u64<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    raw_data: bool,
) -> InstrResult<bool> {
    let expected_args = if raw_data { 3 } else { 2 };
    if args.len() != expected_args {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array_or_data = coerce_vreg_to_i64(ctx, builder, args[0]);
    let length_arg = if raw_data {
        Some(coerce_vreg_to_i64(ctx, builder, args[1]))
    } else {
        None
    };
    let needle_arg = if raw_data { args[2] } else { args[1] };
    let needle = coerce_vreg_to_i64(ctx, builder, needle_arg);
    let zero = builder.ins().iconst(types::I64, 0);
    let one = builder.ins().iconst(types::I64, 1);

    let ptr_bits = if raw_data {
        None
    } else {
        let ptr_mask = builder.ins().iconst(types::I64, !7i64);
        Some(builder.ins().band(array_or_data, ptr_mask))
    };
    let kind_block = if raw_data { None } else { Some(builder.create_block()) };
    let len_block = if raw_data { None } else { Some(builder.create_block()) };
    let loop_block = builder.create_block();
    let chunk_block = builder.create_block();
    let chunk_second_block = builder.create_block();
    let tail_block = builder.create_block();
    let tail_body_block = builder.create_block();
    let found_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(loop_block, types::I64);
    builder.append_block_param(chunk_second_block, types::I64);
    builder.append_block_param(chunk_second_block, types::I64);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(tail_block, types::I64);
    builder.append_block_param(tail_body_block, types::I64);
    builder.append_block_param(tail_body_block, types::I64);
    builder.append_block_param(done_block, types::I64);

    let length: Value;
    if raw_data {
        length = length_arg.unwrap();
        builder.ins().jump(loop_block, &[zero, array_or_data]);
    } else {
        let ptr_bits = ptr_bits.unwrap();
        let kind_block = kind_block.unwrap();
        let len_block = len_block.unwrap();
        let min_heap_value = builder.ins().iconst(types::I64, 4096);
        let too_small = builder.ins().icmp(IntCC::SignedLessThan, array_or_data, min_heap_value);
        builder.ins().brif(too_small, done_block, &[zero], kind_block, &[]);

        builder.switch_to_block(kind_block);
        let tag = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 0);
        let tag64 = builder.ins().uextend(types::I64, tag);
        let is_array = builder.ins().icmp_imm(IntCC::Equal, tag64, 2);
        builder.ins().brif(is_array, len_block, &[], done_block, &[zero]);
        builder.seal_block(kind_block);

        builder.switch_to_block(len_block);
        length = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
        let negative_len = builder.ins().icmp(IntCC::SignedLessThan, length, zero);
        let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
        builder
            .ins()
            .brif(negative_len, done_block, &[zero], loop_block, &[zero, data_ptr]);
        builder.seal_block(len_block);
    }

    builder.switch_to_block(loop_block);
    let idx = builder.block_params(loop_block)[0];
    let cursor = builder.block_params(loop_block)[1];
    let idx_plus_seven = builder.ins().iadd_imm(idx, 7);
    let has_chunk = builder.ins().icmp(IntCC::SignedLessThan, idx_plus_seven, length);
    builder
        .ins()
        .brif(has_chunk, chunk_block, &[], tail_block, &[idx, cursor]);

    builder.switch_to_block(chunk_block);
    let needle_vec = builder.ins().splat(types::I64X2, needle);
    let first_values = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 0);
    let mut hit_mask = vector_compare_mask_i64x2(builder, first_values, needle_vec);
    for offset in [16, 32, 48] {
        let values = builder.ins().load(types::I64X2, MemFlags::new(), cursor, offset);
        let mask = vector_compare_mask_i64x2(builder, values, needle_vec);
        hit_mask = builder.ins().bor(hit_mask, mask);
    }
    let any_hit = builder.ins().vany_true(hit_mask);
    let chunk_hit = builder.ins().icmp_imm(IntCC::NotEqual, any_hit, 0);
    let next_idx = builder.ins().iadd_imm(idx, 8);
    let next_cursor = builder.ins().iadd_imm(cursor, 64);
    builder.ins().brif(
        chunk_hit,
        found_block,
        &[],
        chunk_second_block,
        &[next_idx, next_cursor],
    );
    builder.seal_block(chunk_block);

    builder.switch_to_block(chunk_second_block);
    let idx = builder.block_params(chunk_second_block)[0];
    let cursor = builder.block_params(chunk_second_block)[1];
    let idx_plus_seven = builder.ins().iadd_imm(idx, 7);
    let has_chunk = builder.ins().icmp(IntCC::SignedLessThan, idx_plus_seven, length);
    let second_test_block = builder.create_block();
    builder
        .ins()
        .brif(has_chunk, second_test_block, &[], tail_block, &[idx, cursor]);
    builder.seal_block(chunk_second_block);

    builder.switch_to_block(second_test_block);
    let first_values = builder.ins().load(types::I64X2, MemFlags::new(), cursor, 0);
    let mut hit_mask = vector_compare_mask_i64x2(builder, first_values, needle_vec);
    for offset in [16, 32, 48] {
        let values = builder.ins().load(types::I64X2, MemFlags::new(), cursor, offset);
        let mask = vector_compare_mask_i64x2(builder, values, needle_vec);
        hit_mask = builder.ins().bor(hit_mask, mask);
    }
    let any_hit = builder.ins().vany_true(hit_mask);
    let chunk_hit = builder.ins().icmp_imm(IntCC::NotEqual, any_hit, 0);
    let next_idx = builder.ins().iadd_imm(idx, 8);
    let next_cursor = builder.ins().iadd_imm(cursor, 64);
    builder
        .ins()
        .brif(chunk_hit, found_block, &[], loop_block, &[next_idx, next_cursor]);
    builder.seal_block(second_test_block);
    builder.seal_block(loop_block);

    builder.switch_to_block(tail_block);
    let tail_idx = builder.block_params(tail_block)[0];
    let tail_cursor = builder.block_params(tail_block)[1];
    let has_tail = builder.ins().icmp(IntCC::SignedLessThan, tail_idx, length);
    builder
        .ins()
        .brif(has_tail, tail_body_block, &[tail_idx, tail_cursor], done_block, &[zero]);

    builder.switch_to_block(tail_body_block);
    let tail_idx = builder.block_params(tail_body_block)[0];
    let tail_cursor = builder.block_params(tail_body_block)[1];
    let value = builder.ins().load(types::I64, MemFlags::new(), tail_cursor, 0);
    let hit = builder.ins().icmp(IntCC::Equal, value, needle);
    let next_tail_idx = builder.ins().iadd_imm(tail_idx, 1);
    let next_tail_cursor = builder.ins().iadd_imm(tail_cursor, 8);
    builder
        .ins()
        .brif(hit, found_block, &[], tail_block, &[next_tail_idx, next_tail_cursor]);
    builder.seal_block(tail_body_block);
    builder.seal_block(tail_block);

    builder.switch_to_block(found_block);
    builder.ins().jump(done_block, &[one]);
    builder.seal_block(found_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn compile_inline_typed_bytes_data_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };
    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let byte_ptr = builder.ins().iadd(data_ptr, index);
    let loaded = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
    let widened = builder.ins().uextend(types::I64, loaded);
    ctx.vreg_values.insert(*dest, widened);
    Ok(true)
}

fn compile_inline_typed_words_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);

    let bounds_block = builder.create_block();
    let load_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let index_is_negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let negative_index = builder.ins().iadd(len, index);
        builder.ins().select(index_is_negative, negative_index, index)
    };
    builder.ins().jump(bounds_block, &[]);

    builder.switch_to_block(bounds_block);
    let in_bounds = if index_is_unsigned {
        builder.ins().icmp(IntCC::UnsignedLessThan, normalized_index, len)
    } else {
        let ge_zero = builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
        let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
        builder.ins().band(ge_zero, lt_len)
    };
    builder.ins().brif(in_bounds, load_block, &[], done_block, &[zero]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(load_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().imul_imm(normalized_index, 8);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    // This inliner is reached from typed `[u32]`/`[u64]` array lowering. Values
    // in that lane are stored by the typed push/set paths as tagged integers, so
    // the generated hot path can untag directly instead of rediscovering the slot
    // representation on every read. Generic/mixed arrays still use `rt_index_get`.
    let word = maybe_packed_u64_load_word(builder, ptr_bits, raw, width);
    builder.ins().jump(done_block, &[word]);
    builder.seal_block(load_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    ctx.vreg_values.insert(*dest, result);
    Ok(true)
}

fn u64_packed_condition(builder: &mut FunctionBuilder, header_ptr: Value) -> Value {
    let flags = builder.ins().load(types::I8, MemFlags::new(), header_ptr, 1);
    let flags64 = builder.ins().uextend(types::I64, flags);
    let packed = builder.ins().band_imm(flags64, 0b1_0000);
    builder.ins().icmp_imm(IntCC::NotEqual, packed, 0)
}

fn maybe_packed_u64_load_word(builder: &mut FunctionBuilder, header_ptr: Value, raw: Value, width: i64) -> Value {
    let int_payload = builder.ins().sshr_imm(raw, 3);
    if width == 4 {
        builder.ins().band_imm(int_payload, 0xFFFF_FFFF)
    } else {
        let is_packed = u64_packed_condition(builder, header_ptr);
        builder.ins().select(is_packed, raw, int_payload)
    }
}

fn maybe_packed_u64_store_word(builder: &mut FunctionBuilder, header_ptr: Value, value: Value, width: i64) -> Value {
    let word = if width == 4 {
        builder.ins().band_imm(value, 0xFFFF_FFFF)
    } else {
        value
    };
    let tagged = builder.ins().ishl_imm(word, 3);
    if width == 8 {
        let is_packed = u64_packed_condition(builder, header_ptr);
        builder.ins().select(is_packed, word, tagged)
    } else {
        tagged
    }
}

fn compile_inline_typed_words_unchecked<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    let word = maybe_packed_u64_load_word(builder, ptr_bits, raw, width);
    ctx.vreg_values.insert(*dest, word);
    Ok(true)
}

fn compile_inline_typed_words_data_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    let int_payload = builder.ins().sshr_imm(raw, 3);
    let word = if width == 4 {
        builder.ins().band_imm(int_payload, 0xFFFF_FFFF)
    } else {
        int_payload
    };
    ctx.vreg_values.insert(*dest, word);
    Ok(true)
}

fn compile_inline_typed_words_data_at_checked<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let header_or_array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let header_ptr = builder.ins().band(header_or_array, ptr_mask);
    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[1]);
    let index = coerce_vreg_to_i64(ctx, builder, args[2]);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    let word = maybe_packed_u64_load_word(builder, header_ptr, raw, 8);
    ctx.vreg_values.insert(*dest, word);
    Ok(true)
}

fn compile_inline_typed_words_raw_data_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let raw = builder.ins().load(types::I64, MemFlags::new(), slot_ptr, 0);
    ctx.vreg_values.insert(*dest, raw);
    Ok(true)
}

fn compile_inline_typed_words_u32_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let raw_index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let index = inline_numeric_arg_typed(ctx, builder, args[1], raw_index);
    // The stored value is a raw machine integer in compiled code (user-fn call
    // results carry no vreg_types entry, so the tagged-int heuristic would
    // false-positive on any multiple of 8 — e.g. color3d_pack results written
    // to the engine3d framebuffer arrived as value>>3).
    let value = coerce_vreg_to_i64(ctx, builder, args[2]);
    let zero = builder.ins().iconst(types::I64, 0);
    let false_value = builder.ins().iconst(types::I8, 0);
    let true_value = builder.ins().iconst(types::I8, 1);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let word_mask = builder.ins().iconst(types::I64, 0xFFFF_FFFF);

    let bounds_block = builder.create_block();
    let store_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I8);

    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let index_is_negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
    let negative_index = builder.ins().iadd(len, index);
    let normalized_index = builder.ins().select(index_is_negative, negative_index, index);
    builder.ins().jump(bounds_block, &[]);

    builder.switch_to_block(bounds_block);
    let ge_zero = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
    let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
    let in_bounds = builder.ins().band(ge_zero, lt_len);
    builder
        .ins()
        .brif(in_bounds, store_block, &[], done_block, &[false_value]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().imul_imm(normalized_index, 8);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let masked = builder.ins().band(value, word_mask);
    let tagged = builder.ins().ishl_imm(masked, 3);
    builder.ins().store(MemFlags::new(), tagged, slot_ptr, 0);
    builder.ins().jump(done_block, &[true_value]);
    builder.seal_block(store_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    if let Some(dest) = dest {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn compile_inline_typed_words_push<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let runtime_name = if width == 4 {
        "rt_typed_words_u32_push"
    } else {
        "rt_typed_words_u64_push"
    };
    let Some(&runtime_id) = ctx.runtime_funcs.get(runtime_name) else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let value = coerce_vreg_to_i64(ctx, builder, args[1]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let capacity = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 16);
    let has_capacity = builder.ins().icmp(IntCC::UnsignedLessThan, len, capacity);
    let returns_value = dest.is_some();
    let true_value = if returns_value {
        Some(builder.ins().iconst(types::I8, 1))
    } else {
        None
    };

    let store_block = builder.create_block();
    let grow_block = builder.create_block();
    let done_block = builder.create_block();
    if returns_value {
        builder.append_block_param(done_block, types::I8);
    }
    builder.ins().brif(has_capacity, store_block, &[], grow_block, &[]);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().imul_imm(len, 8);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let stored = maybe_packed_u64_store_word(builder, ptr_bits, value, width);
    builder.ins().store(MemFlags::new(), stored, slot_ptr, 0);
    let next_len = builder.ins().iadd_imm(len, 1);
    builder.ins().store(MemFlags::new(), next_len, ptr_bits, 8);
    if let Some(true_value) = true_value {
        builder.ins().jump(done_block, &[true_value]);
    } else {
        builder.ins().jump(done_block, &[]);
    }
    builder.seal_block(store_block);

    builder.switch_to_block(grow_block);
    let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
    let adapted = adapt_args_to_signature(builder, runtime_ref, vec![array, value]);
    let call = adapted_call(builder, runtime_ref, &adapted);
    if returns_value {
        let result = builder
            .inst_results(call)
            .first()
            .copied()
            .unwrap_or_else(|| true_value.expect("typed word push result constant"));
        builder.ins().jump(done_block, &[result]);
    } else {
        builder.ins().jump(done_block, &[]);
    }
    builder.seal_block(grow_block);

    builder.switch_to_block(done_block);
    let result = dest.map(|_| builder.block_params(done_block)[0]);
    builder.seal_block(done_block);
    if let (Some(dest), Some(result)) = (dest, result) {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn compile_inline_typed_words_push_known_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let value = coerce_vreg_to_i64(ctx, builder, args[2]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let stored = maybe_packed_u64_store_word(builder, ptr_bits, value, width);
    builder.ins().store(MemFlags::new(), stored, slot_ptr, 0);
    let next_len = builder.ins().iadd_imm(index, 1);
    builder.ins().store(MemFlags::new(), next_len, ptr_bits, 8);
    if let Some(dest) = dest {
        let true_value = builder.ins().iconst(types::I8, 1);
        ctx.vreg_values.insert(*dest, true_value);
    }
    Ok(true)
}

fn compile_inline_typed_words_push_known_data_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 4 {
        return Ok(false);
    }

    let header_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[1]);
    let index = coerce_vreg_to_i64(ctx, builder, args[2]);
    let value = coerce_vreg_to_i64(ctx, builder, args[3]);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let stored = maybe_packed_u64_store_word(builder, header_ptr, value, width);
    builder.ins().store(MemFlags::new(), stored, slot_ptr, 0);
    let next_len = builder.ins().iadd_imm(index, 1);
    builder.ins().store(MemFlags::new(), next_len, header_ptr, 8);
    if let Some(dest) = dest {
        let true_value = builder.ins().iconst(types::I8, 1);
        ctx.vreg_values.insert(*dest, true_value);
    }
    Ok(true)
}

fn compile_inline_typed_words_store_known_data_at<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 4 {
        return Ok(false);
    }

    let data_ptr = coerce_vreg_to_i64(ctx, builder, args[1]);
    let index = coerce_vreg_to_i64(ctx, builder, args[2]);
    let value = coerce_vreg_to_i64(ctx, builder, args[3]);
    let slot_offset = builder.ins().ishl_imm(index, 3);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let header_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let stored = maybe_packed_u64_store_word(builder, header_ptr, value, width);
    builder.ins().store(MemFlags::new(), stored, slot_ptr, 0);
    if let Some(dest) = dest {
        let true_value = builder.ins().iconst(types::I8, 1);
        ctx.vreg_values.insert(*dest, true_value);
    }
    Ok(true)
}

fn compile_inline_array_set_len_known<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let header_ptr = coerce_vreg_to_i64(ctx, builder, args[0]);
    let raw_len = coerce_vreg_to_i64(ctx, builder, args[1]);
    let len = inline_numeric_arg_typed(ctx, builder, args[1], raw_len);
    builder.ins().store(MemFlags::new(), len, header_ptr, 8);
    if let Some(dest) = dest {
        let true_value = builder.ins().iconst(types::I8, 1);
        ctx.vreg_values.insert(*dest, true_value);
    }
    Ok(true)
}

fn compile_inline_typed_bytes_u8_push<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(&runtime_id) = ctx.runtime_funcs.get("rt_typed_bytes_u8_push") else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let value = coerce_vreg_to_i64(ctx, builder, args[1]);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let capacity = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 16);
    let has_capacity = builder.ins().icmp(IntCC::UnsignedLessThan, len, capacity);
    let returns_value = dest.is_some();
    let true_value = if returns_value {
        Some(builder.ins().iconst(types::I8, 1))
    } else {
        None
    };

    let store_block = builder.create_block();
    let grow_block = builder.create_block();
    let done_block = builder.create_block();
    if returns_value {
        builder.append_block_param(done_block, types::I8);
    }
    builder.ins().brif(has_capacity, store_block, &[], grow_block, &[]);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let packed_block = builder.create_block();
    let slot_block = builder.create_block();
    let gc_flags = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 1);
    let byte_packed = builder.ins().band_imm(gc_flags, 8);
    let is_byte_packed = builder.ins().icmp_imm(IntCC::NotEqual, byte_packed, 0);
    builder.ins().brif(is_byte_packed, packed_block, &[], slot_block, &[]);
    builder.seal_block(store_block);

    builder.switch_to_block(packed_block);
    let byte_ptr = builder.ins().iadd(data_ptr, len);
    let byte_value = builder.ins().ireduce(types::I8, value);
    builder.ins().store(MemFlags::new(), byte_value, byte_ptr, 0);
    let next_len = builder.ins().iadd_imm(len, 1);
    builder.ins().store(MemFlags::new(), next_len, ptr_bits, 8);
    if let Some(true_value) = true_value {
        builder.ins().jump(done_block, &[true_value]);
    } else {
        builder.ins().jump(done_block, &[]);
    }
    builder.seal_block(packed_block);

    builder.switch_to_block(slot_block);
    let slot_offset = builder.ins().imul_imm(len, 8);
    let slot_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let byte_mask = builder.ins().iconst(types::I64, 0xff);
    let masked = builder.ins().band(value, byte_mask);
    let tagged = builder.ins().ishl_imm(masked, 3);
    builder.ins().store(MemFlags::new(), tagged, slot_ptr, 0);
    let next_len = builder.ins().iadd_imm(len, 1);
    builder.ins().store(MemFlags::new(), next_len, ptr_bits, 8);
    if let Some(true_value) = true_value {
        builder.ins().jump(done_block, &[true_value]);
    } else {
        builder.ins().jump(done_block, &[]);
    }
    builder.seal_block(slot_block);

    builder.switch_to_block(grow_block);
    let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
    let adapted = adapt_args_to_signature(builder, runtime_ref, vec![array, value]);
    let call = adapted_call(builder, runtime_ref, &adapted);
    if returns_value {
        let result = builder
            .inst_results(call)
            .first()
            .copied()
            .unwrap_or_else(|| true_value.expect("typed byte push result constant"));
        builder.ins().jump(done_block, &[result]);
    } else {
        builder.ins().jump(done_block, &[]);
    }
    builder.seal_block(grow_block);

    builder.switch_to_block(done_block);
    let result = dest.map(|_| builder.block_params(done_block)[0]);
    builder.seal_block(done_block);
    if let (Some(dest), Some(result)) = (dest, result) {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn multiply_by_15(builder: &mut FunctionBuilder, value: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    let times_16 = builder.ins().ishl_imm(value, 4);
    builder.ins().isub(times_16, value)
}

fn compile_inline_adler_reduce<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
) -> InstrResult<bool> {
    if args.len() != 1 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let value = coerce_vreg_to_i64(ctx, builder, args[0]);
    let low_mask = builder.ins().iconst(types::I64, 0xFFFF);
    let low = builder.ins().band(value, low_mask);
    let high = builder.ins().ushr_imm(value, 16);
    let high_times_15 = multiply_by_15(builder, high);
    let reduced = builder.ins().iadd(low, high_times_15);
    let low = builder.ins().band(reduced, low_mask);
    let high = builder.ins().ushr_imm(reduced, 16);
    let high_times_15 = multiply_by_15(builder, high);
    let reduced = builder.ins().iadd(low, high_times_15);
    let subtract_modulus = builder
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, reduced, 65521);
    let minus_modulus = builder.ins().iadd_imm(reduced, -65521);
    let selected = builder.ins().select(subtract_modulus, minus_modulus, reduced);
    ctx.vreg_values.insert(*dest, selected);
    Ok(true)
}

fn compile_inline_typed_bytes_le_set_unchecked<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    width: i64,
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let raw_value = coerce_vreg_to_i64(ctx, builder, args[2]);
    let value = inline_numeric_arg_typed(ctx, builder, args[2], raw_value);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let byte_ptr = builder.ins().iadd(data_ptr, index);
    if width == 8 {
        builder.ins().store(MemFlags::new(), value, byte_ptr, 0);
    } else {
        let narrowed = builder.ins().ireduce(types::I32, value);
        builder.ins().store(MemFlags::new(), narrowed, byte_ptr, 0);
    }
    if let Some(dest) = dest {
        ctx.vreg_values.insert(*dest, builder.ins().iconst(types::I8, 1));
    }
    Ok(true)
}

fn compile_inline_bytes_u8_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    args: &[VReg],
    trusted_array: bool,
) -> InstrResult<bool> {
    if args.len() != 3 {
        return Ok(false);
    }

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
    let value = coerce_vreg_to_i64(ctx, builder, args[2]);
    let zero = builder.ins().iconst(types::I64, 0);
    let false_value = builder.ins().iconst(types::I8, 0);
    let true_value = builder.ins().iconst(types::I8, 1);
    let tag_mask = builder.ins().iconst(types::I64, 7);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let byte_mask = builder.ins().iconst(types::I64, 0xff);

    let bounds_block = builder.create_block();
    let store_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I8);

    let ptr_bits = builder.ins().band(array, ptr_mask);
    if trusted_array {
        builder.ins().jump(bounds_block, &[]);
    } else {
        let type_block = builder.create_block();
        let tag = builder.ins().band(array, tag_mask);
        let is_heap = builder.ins().icmp_imm(IntCC::Equal, tag, 1);
        builder.ins().brif(is_heap, type_block, &[], done_block, &[false_value]);

        builder.switch_to_block(type_block);
        let object_type = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 0);
        let is_array = builder.ins().icmp_imm(IntCC::Equal, object_type, 2);
        builder
            .ins()
            .brif(is_array, bounds_block, &[], done_block, &[false_value]);
        builder.seal_block(type_block);
    }

    builder.switch_to_block(bounds_block);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let index_is_negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
    let negative_index = builder.ins().iadd(len, index);
    let normalized_index = builder.ins().select(index_is_negative, negative_index, index);
    let ge_zero = builder
        .ins()
        .icmp(IntCC::SignedGreaterThanOrEqual, normalized_index, zero);
    let lt_len = builder.ins().icmp(IntCC::SignedLessThan, normalized_index, len);
    let in_bounds = builder.ins().band(ge_zero, lt_len);
    builder
        .ins()
        .brif(in_bounds, store_block, &[], done_block, &[false_value]);
    builder.seal_block(bounds_block);

    builder.switch_to_block(store_block);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let byte = builder.ins().band(value, byte_mask);
    if trusted_array {
        let byte_value = builder.ins().ireduce(types::I8, byte);
        let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
        builder.ins().store(MemFlags::new(), byte_value, byte_ptr, 0);
        builder.ins().jump(done_block, &[true_value]);
        builder.seal_block(store_block);

        builder.switch_to_block(done_block);
        let result = builder.block_params(done_block)[0];
        builder.seal_block(done_block);
        if let Some(dest) = dest {
            ctx.vreg_values.insert(*dest, result);
        }
        return Ok(true);
    }

    let packed_block = builder.create_block();
    let slot_block = builder.create_block();
    let gc_flags = builder.ins().load(types::I8, MemFlags::new(), ptr_bits, 1);
    let byte_packed = builder.ins().band_imm(gc_flags, 8);
    let is_byte_packed = builder.ins().icmp_imm(IntCC::NotEqual, byte_packed, 0);
    builder.ins().brif(is_byte_packed, packed_block, &[], slot_block, &[]);
    builder.seal_block(store_block);

    builder.switch_to_block(packed_block);
    let byte_value = builder.ins().ireduce(types::I8, byte);
    let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
    builder.ins().store(MemFlags::new(), byte_value, byte_ptr, 0);
    builder.ins().jump(done_block, &[true_value]);
    builder.seal_block(packed_block);

    builder.switch_to_block(slot_block);
    let slot_offset = builder.ins().imul_imm(normalized_index, 8);
    let elem_ptr = builder.ins().iadd(data_ptr, slot_offset);
    let tagged = builder.ins().ishl_imm(byte, 3);
    builder.ins().store(MemFlags::new(), tagged, elem_ptr, 0);
    builder.ins().jump(done_block, &[true_value]);
    builder.seal_block(slot_block);

    builder.switch_to_block(done_block);
    let result = builder.block_params(done_block)[0];
    builder.seal_block(done_block);
    if let Some(dest) = dest {
        ctx.vreg_values.insert(*dest, result);
    }
    Ok(true)
}

fn coerce_vreg_to_i64<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    vreg: VReg,
) -> cranelift_codegen::ir::Value {
    let value = get_vreg_or_default(ctx, builder, &vreg);
    let ty = builder.func.dfg.value_type(value);
    if ty == types::I64 {
        return value;
    }
    if !ty.is_int() || ty.bits() >= 64 {
        return value;
    }
    if matches!(
        ctx.vreg_types.get(&vreg).copied(),
        Some(TypeId::I8) | Some(TypeId::I16) | Some(TypeId::I32) | Some(TypeId::I64)
    ) {
        builder.ins().sextend(types::I64, value)
    } else {
        builder.ins().uextend(types::I64, value)
    }
}

/// Get the return type for a runtime SFFI function.
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
/// in lowering_expr.rs when passing native integers to SFFI functions.
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

fn runtime_payload_value<M: Module>(
    ctx: &InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    arg: VReg,
) -> cranelift_codegen::ir::Value {
    let value = get_vreg_or_default(ctx, builder, &arg);
    if matches!(
        ctx.vreg_types.get(&arg).copied(),
        Some(
            TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64
                | TypeId::BOOL
        )
    ) {
        tag_int_as_runtime_value(builder, value)
    } else {
        value
    }
}

fn known_enum_variant<'a, M: Module>(ctx: &InstrContext<'_, M>, func_name: &'a str) -> Option<(&'a str, &'a str)> {
    let split = func_name
        .rsplit_once("::")
        .or_else(|| func_name.rsplit_once('.'))
        .or_else(|| func_name.rsplit_once("_dot_"))?;
    let enum_name = split.0;
    let variant_name = split.1;
    let enum_tail = enum_name
        .rsplit_once('.')
        .map(|(_, tail)| tail)
        .unwrap_or_else(|| enum_name.rsplit("__").next().unwrap_or(enum_name));
    let variants = ctx.enum_defs.get(enum_name).or_else(|| ctx.enum_defs.get(enum_tail))?;
    variants
        .iter()
        .any(|(candidate, _)| candidate == variant_name)
        .then_some((enum_name, variant_name))
}

fn unresolved_enum_constructor_variant(func_name: &str) -> Option<(&str, &str)> {
    let (type_name, variant_name) = func_name.rsplit_once("::")?;
    let type_tail = type_name
        .rsplit_once('.')
        .map(|(_, tail)| tail)
        .unwrap_or_else(|| type_name.rsplit("__").next().unwrap_or(type_name));
    let type_head_is_upper = type_tail.chars().next().is_some_and(|c| c.is_ascii_uppercase());
    let variant_head_is_upper = variant_name.chars().next().is_some_and(|c| c.is_ascii_uppercase());
    (type_head_is_upper && variant_head_is_upper).then_some((type_name, variant_name))
}

fn compile_known_enum_constructor_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    enum_name: &str,
    variant_name: &str,
    args: &[VReg],
) -> bool {
    let Some(dest) = dest else {
        return true;
    };

    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    variant_name.hash(&mut hasher);
    let disc = (hasher.finish() & 0xFFFFFFFF) as i64;
    let enum_id_val = builder
        .ins()
        .iconst(types::I32, i64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)));
    let disc_val = builder.ins().iconst(types::I32, disc);
    let payload_val = match args {
        [] => builder.ins().iconst(types::I64, 3),
        // Single-payload construction must tag scalars exactly like the
        // multi-arg path (runtime_payload_value) so that extraction — which
        // assumes the tagged convention — recovers the value. Storing a raw
        // scalar here made `Ok(42).unwrap()` untag to 5, floats read as raw
        // bits, bools as nil. Heap payloads (text) pass through unchanged.
        // Task #117 / #109.
        [single] => runtime_payload_value(ctx, builder, *single),
        many => {
            let capacity = builder.ins().iconst(types::I64, many.len() as i64);
            let array = call_runtime_1(ctx, builder, "rt_array_new", capacity);
            for arg in many {
                let payload = runtime_payload_value(ctx, builder, *arg);
                let _ = call_runtime_2(ctx, builder, "rt_array_push", array, payload);
            }
            array
        }
    };
    let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id_val, disc_val, payload_val);
    ctx.vreg_values.insert(*dest, result);
    true
}

/// Check if a runtime function returns a raw integer that should be tagged as a RuntimeValue.
/// These are runtime functions whose C ABI returns an unboxed integer, while the
/// native Simple value path expects tagged integer values in vregs.
///
/// NOTE: rt_array_get, rt_tuple_get, rt_index_get, rt_dict_get, and rt_pool_join
/// are NOT included here because they return RuntimeValue that could be any type
/// (or a closure result already encoded as a RuntimeValue), not just integers.
/// Untagging should be done based on the expected result type, not the function
/// name. The caller should handle type-specific untagging.
fn needs_runtime_value_result_tagging<M: Module>(ctx: &InstrContext<'_, M>, func_name: &str) -> bool {
    ctx.tag_runtime_pool_join_result && func_name == "rt_pool_join"
}

/// Returns which Simple-level argument indices are text parameters for a given
/// runtime SFFI function. Text arguments are RuntimeValue strings that must be
/// expanded to (ptr, len) pairs when calling the C-ABI SFFI function.
///
pub fn text_arg_indices(func_name: &str) -> Option<&'static [usize]> {
    match func_name {
        // Print/IO (text → ptr, len)
        "rt_print_str" | "rt_println_str" | "rt_eprint_str" | "rt_eprintln_str" => Some(&[0]),

        // Environment variables
        "rt_env_get" | "rt_env_get_i64" | "rt_get_env" | "rt_env_exists" | "rt_env_remove" => Some(&[0]),
        "rt_env_set" | "rt_set_env" => Some(&[0, 1]),
        "rt_lexer_source_set" => Some(&[0]),

        // File I/O (single path)
        "rt_crc32_text"
        | "rt_file_exists"
        | "rt_file_canonicalize"
        | "rt_file_read_text"
        | "rt_file_size"
        | "rt_file_hash_sha256"
        | "rt_file_fsync"
        | "rt_file_fsync_cached"
        | "rt_file_sync"
        | "rt_file_delete"
        | "rt_file_remove"
        | "rt_file_read_lines"
        | "rt_file_read_bytes"
        | "rt_file_mmap_read_text"
        | "rt_file_mmap_len"
        | "rt_file_mmap_read_bytes" => Some(&[0]),
        // File I/O (two text params: path + content, or src + dest)
        // rt_file_write_text / rt_file_append_text take (ptr,len) PAIRS
        // (see runtime file_ops.rs); they were wrongly in text_cstr_arg_indices,
        // which passes ptr-only and made every JIT write_file return false.
        "rt_file_write_text"
        | "rt_file_append_text"
        | "rt_file_copy"
        | "rt_file_rename"
        | "rt_file_move"
        | "rt_file_wrap_smf_dynlib"
        | "rt_file_extract_smf_dynlib"
        | "rt_file_create_excl" => Some(&[0, 1]),
        "rt_file_write_bytes" => Some(&[0]),

        // Directory operations
        "rt_dir_list" | "rt_dir_remove_all" | "rt_dir_glob" | "rt_dir_walk" | "rt_set_current_dir"
        | "rt_dir_exists" => Some(&[0]),
        // rt_dir_create/rt_dir_create_all/rt_dir_remove take (path_ptr, path_len[, recursive]) —
        // the linked runtime (runtime/src/value/sffi/file_io/directory.rs) needs
        // the explicit length, not just a null-terminated pointer. These were
        // wrongly in text_cstr_arg_indices below, which dropped path_len and
        // shifted `recursive` into the length's register slot (same class of
        // bug as the rt_process_run arg-shift fix in expand_process_c_runtime_args).
        "rt_dir_create" | "rt_dir_create_all" | "rt_dir_remove" => Some(&[0]),
        "rt_file_find" => Some(&[0, 1]),

        // Async I/O driver text arguments
        "rt_driver_submit_open" => Some(&[1]),
        "rt_driver_submit_connect" | "rt_driver_submit_send" | "rt_driver_submit_write" => Some(&[2]),

        // Path operations (single path)
        "rt_path_basename" | "rt_path_dirname" | "rt_path_ext" | "rt_path_absolute" | "rt_path_stem"
        | "rt_path_parent" => Some(&[0]),
        // Path operations (two paths)
        "rt_path_relative" | "rt_path_join" => Some(&[0, 1]),

        // Contract checking (func_name is text at different positions)
        "simple_contract_check" => Some(&[2]),
        "simple_contract_check_msg" => Some(&[2, 3]),
        "rt_contract_violation_new" => Some(&[1, 2]),

        // Interpreter bridge
        "rt_interp_call" => Some(&[0]),

        // SFFI object system (method name at index 1)
        "rt_sffi_call_method" | "rt_sffi_has_method" | "rt_sffi_object_call_method" | "rt_sffi_object_has_method" => {
            Some(&[1])
        }
        "rt_sffi_type_register" => Some(&[0]),

        // BDD test framework
        "rt_bdd_describe_start" | "rt_bdd_it_start" | "rt_bdd_expect_fail" => Some(&[0]),

        // Networking (address is text)
        "native_tcp_bind" | "native_tcp_connect" | "native_udp_bind" => Some(&[0]),
        "native_tcp_connect_timeout" => Some(&[0]),
        "native_tcp_read"
        | "native_tcp_write"
        | "native_tcp_peek"
        | "native_udp_recv_from"
        | "native_udp_recv"
        | "native_udp_send"
        | "native_udp_peek_from"
        | "native_udp_peek" => Some(&[1]),
        "native_udp_connect" => Some(&[1]),
        "native_udp_send_to" => Some(&[1, 2]),

        // Regex (pattern and text)
        "sffi_regex_is_match"
        | "sffi_regex_find"
        | "sffi_regex_find_all"
        | "sffi_regex_captures"
        | "sffi_regex_split" => Some(&[0, 1]),
        "sffi_regex_replace" | "sffi_regex_replace_all" => Some(&[0, 1, 2]),
        "sffi_regex_split_n" => Some(&[0, 1]),

        // File stat (path is text, rest are output pointers)
        "rt_file_stat" => Some(&[0]),

        // Hosted compositor (Cocoa / Win32 windows take title text at index 2)
        "rt_cocoa_window_new" | "rt_win32_window_new" => Some(&[2]),

        _ => None,
    }
}

/// Text args that need only a null-terminated C pointer (no length).
/// These functions accept `*const c_char` and the runtime guarantees null termination.
pub fn text_cstr_arg_indices(func_name: &str) -> Option<&'static [usize]> {
    match func_name {
        // NOTE: rt_process_run/rt_process_spawn/rt_process_execute/rt_process_run_timeout
        // are intentionally NOT listed here — they are handled by
        // process_c_runtime_arg_indices (checked before this table), which now
        // expands cmd to a (ptr, len) pair to match the linked runtime's actual
        // signature (compiler_rust/runtime/src/value/sffi/env_process.rs).
        "rt_cuda_launch_kernel" => Some(&[1]),
        "rt_cuda_module_load_data" => Some(&[0]),
        // Fast in-memory DB: C functions accept const char* for string params
        "rt_db_table_create" => Some(&[0]),   // name
        "rt_db_put" => Some(&[1]),            // pk_text
        "rt_db_get" => Some(&[1]),            // pk_text
        "rt_db_delete" => Some(&[1]),         // pk_text
        "rt_db_put_row3" => Some(&[1]),       // pk
        "rt_db_get_int_by_pk" => Some(&[1]),  // pk
        "rt_db_update_int" => Some(&[1]),     // pk
        "rt_db_update_text" => Some(&[1, 3]), // pk, value
        "rt_db_put_value_text" => Some(&[3]), // value
        _ => None,
    }
}

fn process_c_runtime_arg_indices(func_name: &str) -> Option<(&'static [usize], &'static [usize])> {
    match func_name {
        "rt_process_run"
        | "rt_process_spawn"
        | "rt_process_execute"
        | "rt_process_run_timeout"
        | "rt_process_run_bounded" => Some((&[0], &[1])),
        _ => None,
    }
}

/// Expand text RuntimeValue arguments to (ptr, len) pairs for SFFI calls.
///
/// Given the original Simple-level argument values and the text_indices specification,
/// this expands each text argument into two values by calling rt_string_data and
/// rt_string_len at runtime. Non-text arguments are passed through unchanged.
fn expand_text_args<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    arg_vals: &[cranelift_codegen::ir::Value],
    text_indices: &[usize],
) -> Vec<cranelift_codegen::ir::Value> {
    let string_data_id = ctx.runtime_funcs["rt_string_data"];
    let string_len_id = ctx.runtime_funcs["rt_string_len"];
    let string_data_ref = ctx.module.declare_func_in_func(string_data_id, builder.func);
    let string_len_ref = ctx.module.declare_func_in_func(string_len_id, builder.func);

    let mut expanded = Vec::with_capacity(arg_vals.len() + text_indices.len());
    for (i, &val) in arg_vals.iter().enumerate() {
        if text_indices.contains(&i) {
            // Expand text RuntimeValue to (ptr, len) pair
            let ptr_call = adapted_call(builder, string_data_ref, &[val]);
            let ptr = builder.inst_results(ptr_call)[0];
            let len_call = adapted_call(builder, string_len_ref, &[val]);
            let len = builder.inst_results(len_call)[0];
            expanded.push(ptr);
            expanded.push(len);
        } else {
            expanded.push(val);
        }
    }
    expanded
}

/// Expand text RuntimeValue arguments to just a C-string pointer (no length).
/// For functions that accept `*const c_char` — strings are null-terminated by the runtime.
fn expand_text_cstr_args<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    arg_vals: &[cranelift_codegen::ir::Value],
    cstr_indices: &[usize],
) -> Vec<cranelift_codegen::ir::Value> {
    let string_data_id = ctx.runtime_funcs["rt_string_data"];
    let string_data_ref = ctx.module.declare_func_in_func(string_data_id, builder.func);

    let mut expanded = Vec::with_capacity(arg_vals.len());
    for (i, &val) in arg_vals.iter().enumerate() {
        if cstr_indices.contains(&i) {
            let ptr_call = adapted_call(builder, string_data_ref, &[val]);
            let ptr = builder.inst_results(ptr_call)[0];
            expanded.push(ptr);
        } else {
            expanded.push(val);
        }
    }
    expanded
}

fn expand_process_c_runtime_args<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    arg_vals: &[cranelift_codegen::ir::Value],
    cstr_indices: &[usize],
    _array_indices: &[usize],
) -> Vec<cranelift_codegen::ir::Value> {
    // The cmd argument is a Simple `text` value; the linked native runtime
    // (compiler_rust/runtime/src/value/sffi/env_process.rs, e.g. rt_process_run)
    // takes an explicit (ptr, len) pair for it, not a bare null-terminated C
    // string. Using expand_text_cstr_args here dropped the length argument
    // entirely, shifting every later argument into the wrong register and
    // leaving the final register uninitialized — manifesting as an
    // exit_group(-8) crash on `simple -c` (self-exec-guard shells out via
    // rt_process_run). Use the normal (ptr, len) expansion instead.
    //
    // The args array argument is passed through UNMASKED (2026-07-11 fix):
    // it previously had its low 3 tag bits stripped (`& !7`), which turned
    // the TAG_HEAP(0b001) RuntimeValue into a TAG_INT value — the Rust
    // runtime's rt_process_run (args: RuntimeValue → rt_array_len →
    // as_typed_ptr) then rejected it and silently ran the command with ZERO
    // args (stage4 full-CLI `run`/`-c` fell through to the interactive
    // REPL because delegation to the sibling seed lost its argv). The
    // core-C runtime needs no mask either: rt_core_as_array accepts both
    // tagged and raw aligned pointers (runtime_native.c).
    expand_text_args(ctx, builder, arg_vals, cstr_indices)
}

fn expand_file_write_bytes_args<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    arg_vals: &[cranelift_codegen::ir::Value],
) -> Option<Vec<cranelift_codegen::ir::Value>> {
    if arg_vals.len() != 2 {
        return None;
    }

    let string_data_id = ctx.runtime_funcs["rt_string_data"];
    let string_len_id = ctx.runtime_funcs["rt_string_len"];
    let string_data_ref = ctx.module.declare_func_in_func(string_data_id, builder.func);
    let string_len_ref = ctx.module.declare_func_in_func(string_len_id, builder.func);

    let path_ptr_call = adapted_call(builder, string_data_ref, &[arg_vals[0]]);
    let path_ptr = builder.inst_results(path_ptr_call)[0];
    let path_len_call = adapted_call(builder, string_len_ref, &[arg_vals[0]]);
    let path_len = builder.inst_results(path_len_call)[0];
    let array_data_id = ctx.runtime_funcs["rt_array_data_ptr_u8"];
    let array_len_id = ctx.runtime_funcs["rt_array_len"];
    let array_data_ref = ctx.module.declare_func_in_func(array_data_id, builder.func);
    let array_len_ref = ctx.module.declare_func_in_func(array_len_id, builder.func);
    let data_ptr_call = adapted_call(builder, array_data_ref, &[arg_vals[1]]);
    let data_ptr = builder.inst_results(data_ptr_call)[0];
    let data_len_call = adapted_call(builder, array_len_ref, &[arg_vals[1]]);
    let data_len = builder.inst_results(data_len_call)[0];

    Some(vec![path_ptr, path_len, data_ptr, data_len])
}

/// Adapt argument values to match a function's expected signature.
/// Handles count mismatches (padding/truncating) and type mismatches (casting).
///
/// Backward-compatible wrapper: widens narrow integers via `uextend` (the old
/// behavior). For signedness-aware widening, call
/// [`adapt_args_to_signature_with_signedness`] and pass per-arg signedness
/// hints from `vreg_types`.
pub(crate) fn adapt_args_to_signature(
    builder: &mut FunctionBuilder,
    func_ref: cranelift_codegen::ir::FuncRef,
    arg_vals: Vec<cranelift_codegen::ir::Value>,
) -> Vec<cranelift_codegen::ir::Value> {
    adapt_args_to_signature_with_signedness(builder, func_ref, arg_vals, None)
}

/// FR-DRIVER-0002b: VReg-aware variant of [`adapt_args_to_signature`].
///
/// `arg_signed[i] == Some(true)` → widen arg `i` via `sextend`. `Some(false)`
/// or missing → widen via `uextend` (the legacy default). Pass the slice from
/// a per-call `vreg_is_signed` lookup when the call site has VRegs in scope.
pub(crate) fn adapt_args_to_signature_with_signedness(
    builder: &mut FunctionBuilder,
    func_ref: cranelift_codegen::ir::FuncRef,
    arg_vals: Vec<cranelift_codegen::ir::Value>,
    arg_signed: Option<&[Option<bool>]>,
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
                // Integer width conversion. FR-DRIVER-0002b: pick sextend for
                // signed VRegs, uextend otherwise (or when no hint is given —
                // preserves legacy unsigned-widen default for runtime/SFFI
                // boundaries).
                if actual_ty.bits() < expected_ty.bits() {
                    let signed = arg_signed.and_then(|s| s.get(i).copied()).flatten().unwrap_or(false);
                    if signed {
                        adapted.push(builder.ins().sextend(expected_ty, val));
                    } else {
                        adapted.push(builder.ins().uextend(expected_ty, val));
                    }
                } else {
                    adapted.push(builder.ins().ireduce(expected_ty, val));
                }
            } else if actual_ty.is_int() && expected_ty.is_float() {
                // Int to float conversion
                adapted.push(builder.ins().fcvt_from_sint(expected_ty, val));
            } else if actual_ty.is_float() && expected_ty.is_int() {
                // Float to int: bitcast to preserve bits (for RuntimeValue tagging)
                if actual_ty == types::F64 && expected_ty == types::I64 {
                    adapted.push(builder.ins().bitcast(types::I64, MemFlags::new(), val));
                } else if actual_ty == types::F32 && expected_ty == types::I64 {
                    // Widen first — an i64 param here is a RuntimeValue slot,
                    // so preserve bits (promote+bitcast), don't value-convert.
                    let promoted = builder.ins().fpromote(types::F64, val);
                    adapted.push(builder.ins().bitcast(types::I64, MemFlags::new(), promoted));
                } else {
                    adapted.push(builder.ins().fcvt_to_sint(expected_ty, val));
                }
            } else if actual_ty.is_float() && expected_ty.is_float() {
                // Float width conversion
                if actual_ty.bits() < expected_ty.bits() {
                    adapted.push(builder.ins().fpromote(expected_ty, val));
                } else {
                    adapted.push(builder.ins().fdemote(expected_ty, val));
                }
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

/// Map a Simple-facing call name to its canonical runtime SFFI name.
///
/// Returns `Some(canonical)` when the name is an alias that should be
/// resolved to a different runtime symbol (e.g., `rt_file_delete` →
/// `rt_file_remove`).  Returns `None` when no alias applies.
///
/// This table must stay in sync with the `sffi_name` match in
/// `compile_call` below and with the alias wrappers in
/// `simple_common::runtime_symbols::RUNTIME_SYMBOL_NAMES`.
pub fn sffi_alias_target(name: &str) -> Option<&'static str> {
    match name {
        "sys_get_args" => Some("rt_get_args"),
        "sys_exit" => Some("rt_exit"),
        "rt_file_read_text" => Some("rt_file_read_text_rv"),
        "rt_file_delete" => Some("rt_file_remove"),
        // Dict-literal lowering emits rt_dict_insert(dict, key, value), but the
        // runtime defines only rt_dict_set (same 3-arg shape); without this the
        // cranelift path declared an undefined import and dict literals could
        // not JIT (the LLVM backend has the same remap inline). cf.
        // mir/lower/lowering_expr_collection.rs, runtime/src/value/dict.rs.
        "rt_dict_insert" => Some("rt_dict_set"),
        "rt_println" => Some("rt_println_value"),
        "rt_print" => Some("rt_print_value"),
        "dealloc" | "free" => Some("rt_free"),
        "len" | "length" => Some("rt_len"),
        "to_text" | "to_string" | "str" => Some("rt_to_string"),
        "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
        "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
        _ => None,
    }
}

/// Compile Call instruction: dispatches to user-defined, built-in I/O, or runtime SFFI functions
///
/// This handles three types of function calls:
/// 1. Built-in I/O functions (print, println, etc.) - handled via compile_builtin_io_call
/// 2. User-defined functions - looked up in func_ids
/// 3. Runtime SFFI functions - looked up in runtime_funcs
pub fn compile_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    target: &CallTarget,
    args: &[VReg],
) -> InstrResult<()> {
    let func_name_raw = target.name();
    // For runtime SFFI matching only, strip module prefix to find the base function name.
    // e.g., "compiler__driver__driver_types__rt_file_read_text" → "rt_file_read_text"
    let func_name_for_sffi = func_name_raw
        .rsplit_once("__")
        .map(|(_, tail)| tail)
        .unwrap_or(func_name_raw);
    // Map Simple builtin names to runtime SFFI function names (for SFFI lookup only)
    // Note: "str", "int", "input" are handled in compile_builtin_io_call, not here
    // The alias table is shared with referenced_call_names via sffi_alias_target().
    let sffi_name: &str = sffi_alias_target(func_name_for_sffi).unwrap_or(func_name_for_sffi);
    // Use raw name for user-function lookups (func_ids, use_map, import_map)
    // but mapped SFFI name for runtime_funcs and builtin I/O checks
    let func_name: &str = func_name_raw;
    // Handle only the true Result/Option constructors. A custom enum may use
    // the same variant leaves and must retain its qualified custom type ID.
    let split_variant = func_name
        .rsplit_once("::")
        .or_else(|| func_name.rsplit_once('.'));
    let (enum_owner, variant_name) = split_variant
        .map(|(owner, variant)| (Some(owner), variant))
        .unwrap_or((None, func_name));
    let builtin_enum_id = match (enum_owner, variant_name) {
        (None | Some("Result"), "Ok" | "Err") => Some(0),
        (None | Some("Option"), "Some" | "None") => Some(1),
        _ => None,
    };
    if let Some(builtin_enum_id) = builtin_enum_id {
        if let Some(d) = dest {
            // Use hashed discriminants consistently with pattern matching
            let disc = {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let mut hasher = DefaultHasher::new();
                variant_name.hash(&mut hasher);
                (hasher.finish() & 0xFFFFFFFF) as i64
            };
            let enum_id_val = builder.ins().iconst(types::I32, builtin_enum_id);
            let disc_val = builder.ins().iconst(types::I32, disc);
            let payload_val = if !args.is_empty() {
                // Tag scalar payloads (Ok/Err/Some) to match the multi-arg /
                // extraction convention; heap payloads pass through. Task #117.
                runtime_payload_value(ctx, builder, args[0])
            } else {
                // Empty payload uses tagged nil (3), not raw 0
                builder.ins().iconst(types::I64, 3)
            };
            let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id_val, disc_val, payload_val);
            ctx.vreg_values.insert(*d, result);
        }
        return Ok(());
    }

    if compile_simple_runtime_memory_intrinsic(ctx, builder, dest, func_name_for_sffi, args)? {
        return Ok(());
    }
    if compile_inline_ctype_call(ctx, builder, dest, func_name, sffi_name, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_data_ptr" && compile_inline_array_data_ptr(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_header_ptr" && compile_inline_array_header_ptr(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_get" && compile_inline_array_get(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_get_text" && compile_inline_array_get_word(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_set" && compile_inline_array_set(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_array_set_text" && compile_inline_array_set_word(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_numeric_xor_sum_u64_data" && compile_inline_numeric_xor_sum_u64(ctx, builder, dest, args, true)?
    {
        return Ok(());
    }
    if sffi_name == "rt_numeric_xor_sum_u64" && compile_inline_numeric_xor_sum_u64(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if sffi_name == "rt_numeric_contains_u64_data"
        && compile_inline_numeric_contains_u64(ctx, builder, dest, args, true)?
    {
        return Ok(());
    }
    if sffi_name == "rt_numeric_contains_u64" && compile_inline_numeric_contains_u64(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if sffi_name == "rt_hash_text" && compile_inline_hash_text(ctx, builder, dest, args)? {
        return Ok(());
    }
    if matches!(sffi_name, "rt_array_set_len_known" | "rt_array_set_len_known_text")
        && compile_inline_array_set_len_known(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if matches!(sffi_name, "rt_len" | "rt_array_len")
        && compile_inline_len(ctx, builder, dest, args, sffi_name == "rt_array_len")?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u8_at" && compile_inline_bytes_u8_at(ctx, builder, dest, args, true)? {
        return Ok(());
    }
    if sffi_name == "rt_bytes_u8_at" && compile_inline_bytes_u8_at(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u32_le_at" && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u64_le_at" && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u32_le_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u64_le_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u8_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 1)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u8_data_at" && compile_inline_typed_bytes_data_at(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_at" && compile_inline_typed_words_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_at" && compile_inline_typed_words_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_unchecked" && compile_inline_typed_words_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_unchecked" && compile_inline_typed_words_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_data_at" && compile_inline_typed_words_data_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_data_at" && compile_inline_typed_words_data_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_data_at_checked"
        && compile_inline_typed_words_data_at_checked(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_raw_data_at"
        && compile_inline_typed_words_raw_data_at(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_set" && compile_inline_typed_words_u32_set(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_push" && compile_inline_typed_words_push(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_push" && compile_inline_typed_words_push(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_push_known_at"
        && compile_inline_typed_words_push_known_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_push_known_at"
        && compile_inline_typed_words_push_known_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_push_known_data_at"
        && compile_inline_typed_words_push_known_data_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_push_known_data_at"
        && compile_inline_typed_words_push_known_data_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u32_store_known_data_at"
        && compile_inline_typed_words_store_known_data_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_words_u64_store_known_data_at"
        && compile_inline_typed_words_store_known_data_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u8_push" && compile_inline_typed_bytes_u8_push(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "_adler_reduce" && compile_inline_adler_reduce(ctx, builder, dest, args)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u32_le_set"
        && compile_inline_typed_bytes_le_set_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u64_le_set"
        && compile_inline_typed_bytes_le_set_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if sffi_name == "rt_bytes_u32_le_at" && compile_inline_bytes_le_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if sffi_name == "rt_bytes_u64_le_at" && compile_inline_bytes_le_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if sffi_name == "rt_typed_bytes_u8_set" && compile_inline_bytes_u8_set(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if sffi_name == "rt_bytes_u8_set" && compile_inline_bytes_u8_set(ctx, builder, dest, args, false)? {
        return Ok(());
    }

    // Handle __get_global_<name> calls (from lower_lvalue GPU path)
    // These return the ADDRESS of the global data object for subsequent Store.
    if let Some(global_name) = func_name.strip_prefix("__get_global_") {
        if let Some(global_id) = ctx.global_ids.get(global_name) {
            let global_ref = ctx.module.declare_data_in_func(*global_id, builder.func);
            let global_addr = builder.ins().global_value(types::I64, global_ref);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, global_addr);
            }
            return Ok(());
        }
        // Try with module prefix (mangled globals: "module__varname")
        let mangled_suffix = format!("__{}", global_name);
        let found = ctx.global_ids.iter().find(|(key, _)| key.ends_with(&mangled_suffix));
        if let Some((_, id)) = found {
            let global_ref = ctx.module.declare_data_in_func(*id, builder.func);
            let global_addr = builder.ins().global_value(types::I64, global_ref);
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, global_addr);
            }
            return Ok(());
        }
        // Fall through to normal call resolution (will auto-stub if not found)
    }

    // Check if this is a built-in I/O function (print, println, etc.)
    // Use sffi_name for builtin/runtime checks since these match on short names
    if let Some(result) = compile_builtin_io_call(ctx, builder, sffi_name, args, dest)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
    } else if has_defined_local_function(ctx, func_name) {
        // Compiler-owned intrinsics above remain authoritative because MIR
        // does not yet carry call origin. For the ordinary SFFI path, a
        // source-defined body owns its name and ABI; empty extern declarations
        // remain imports and continue through the runtime path below.
        let callee_id = ctx.func_ids[func_name];
        compile_user_function_call(ctx, builder, dest, func_name, args, callee_id)?;
    } else if let Some(&runtime_id) = ctx.runtime_funcs.get(sffi_name) {
        // Runtime imports need SFFI-specific tagging and text expansion.
        if !is_profiler_function(sffi_name) {
            emit_profiler_call(ctx, builder, sffi_name)?;
        }
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);

        // Check if this function needs RuntimeValue tagging for certain arguments
        let tagging_indices = needs_runtime_value_tagging(sffi_name);
        // Check if this function returns a raw value that needs Simple tagging.
        let needs_tagging = needs_runtime_value_result_tagging(ctx, sffi_name);

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
        let arg_vals = reinterpret_float_bit_args(ctx, builder, args, arg_vals);

        // Expand text RuntimeValue arguments for C-ABI SFFI calls.
        // Two modes: (ptr, len) for Rust-style APIs, or ptr-only for C-string APIs.
        let arg_vals = if sffi_name == "rt_file_write_bytes" {
            expand_file_write_bytes_args(ctx, builder, &arg_vals).unwrap_or(arg_vals)
        } else if let Some((cstr_indices, array_indices)) = process_c_runtime_arg_indices(sffi_name) {
            expand_process_c_runtime_args(ctx, builder, &arg_vals, cstr_indices, array_indices)
        } else if let Some(text_indices) = text_arg_indices(sffi_name) {
            expand_text_args(ctx, builder, &arg_vals, text_indices)
        } else if let Some(cstr_indices) = text_cstr_arg_indices(sffi_name) {
            expand_text_cstr_args(ctx, builder, &arg_vals, cstr_indices)
        } else {
            arg_vals
        };

        let arg_signed: Vec<Option<bool>> = args.iter().map(|arg| super::core::vreg_is_signed(ctx, *arg)).collect();
        let arg_vals = adapt_args_to_signature_with_signedness(builder, runtime_ref, arg_vals, Some(&arg_signed));
        let call = adapted_call(builder, runtime_ref, &arg_vals);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                let mut result = results[0];

                // Extend smaller return types to i64 (the standard vreg type)
                // This is needed because some SFFI functions return i32 (e.g., rt_exec)
                // but all vregs are expected to be i64.
                //
                // FR-DRIVER-0002b: if the destination VReg is declared signed,
                // use `sextend` so negative runtime-returned narrow values keep
                // their sign. Unsigned and unknown destinations keep the old
                // `uextend` (zero-extend) behavior — this preserves Rust-SFFI
                // contracts where values like `u32 = 0xFFFFFFFF` must not
                // sign-extend to `-1` when consumed as `i64`.
                let dest_signed = super::core::vreg_is_signed(ctx, *d) == Some(true);
                if let Some(ret_type) = get_runtime_return_type(sffi_name) {
                    if ret_type == types::I32 || ret_type == types::I8 {
                        result = if dest_signed {
                            builder.ins().sextend(types::I64, result)
                        } else {
                            builder.ins().uextend(types::I64, result)
                        };
                    }
                }

                // Tag the result if needed.
                let final_result = if needs_tagging {
                    tag_int_as_runtime_value(builder, result)
                } else {
                    result
                };
                ctx.vreg_values.insert(*d, final_result);
            } else {
                ctx.vreg_values.insert(*d, builder.ins().iconst(types::I64, 0));
            }
        }
        if !is_profiler_function(sffi_name) {
            emit_profiler_return(ctx, builder)?;
        }
    } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
        compile_user_function_call(ctx, builder, dest, func_name, args, callee_id)?;
    } else {
        if let Some((enum_name, variant_name)) = known_enum_variant(ctx, func_name) {
            if compile_known_enum_constructor_call(ctx, builder, dest, enum_name, variant_name, args) {
                return Ok(());
            }
        } else if let Some((enum_name, variant_name)) = unresolved_enum_constructor_variant(func_name) {
            if compile_known_enum_constructor_call(ctx, builder, dest, enum_name, variant_name, args) {
                return Ok(());
            }
        }

        // Before falling through to cross-module import, check if this is a qualified
        // builtin method call like "ALPHA_LOWER.contains" or "items.push".
        // The parser sometimes treats `val.method(args)` as a qualified function call
        // when it can't resolve the receiver type. Map the method part to the
        // corresponding runtime function.
        if let Some(dot_pos) = func_name.rfind('.') {
            let method_part = &func_name[dot_pos + 1..];
            if method_part == "merge" && args.len() == 2 {
                let receiver_val = get_vreg_or_default(ctx, builder, &args[0]);
                let other_val = get_vreg_or_default(ctx, builder, &args[1]);
                let count = inline_runtime_array_len_value(builder, other_val);
                if let Some(&func_id) = ctx.runtime_funcs.get("rt_array_extend_i64") {
                    let runtime_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    adapted_call(builder, runtime_ref, &[receiver_val, other_val, count]);
                    if let Some(d) = dest {
                        ctx.vreg_values.insert(*d, receiver_val);
                    }
                    return Ok(());
                }
            }
            let runtime_func: Option<&str> = match method_part {
                "contains" | "contains_key" | "has_key" => Some("rt_contains"),
                "len" | "length" => Some("rt_len"),
                "starts_with" => Some("rt_string_starts_with"),
                "ends_with" => Some("rt_string_ends_with"),
                "concat" => Some("rt_string_concat"),
                "char_at" | "at" => Some("rt_string_char_at"),
                "char_code_at" => Some("rt_string_char_code_at"),
                "push" => Some("rt_array_push"),
                "pop" => Some("rt_array_pop"),
                "clear" => Some("rt_array_clear"),
                "join" => Some("rt_string_join"),
                "trim" => Some("rt_string_trim"),
                "trim_start" => Some("rt_string_trim_start"),
                "trim_end" => Some("rt_string_trim_end"),
                "split" => Some("rt_string_split"),
                "bytes" => Some("rt_string_bytes"),
                "chars" => Some("rt_string_chars"),
                "replace" => Some("rt_string_replace"),
                "to_upper" | "upper" => Some("rt_string_to_upper"),
                "to_lower" | "lower" => Some("rt_string_to_lower"),
                "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
                "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
                "index_of" | "find" | "find_str" => Some("rt_string_find"),
                "rfind" | "last_index_of" => Some("rt_string_rfind"),
                "to_string" | "to_text" | "str" => Some("rt_to_string"),
                "slice" | "substring" => Some("rt_slice"),
                "get" => Some("rt_index_get"),
                "keys" => Some("rt_dict_keys"),
                "values" => Some("rt_dict_values"),
                "filter" => Some("rt_array_filter"),
                "sort" => Some("rt_array_sort"),
                "reverse" => Some("rt_array_reverse"),
                "first" => Some("rt_array_first"),
                "last" => Some("rt_array_last"),
                "find" => Some("rt_array_find"),
                "any" => Some("rt_array_any"),
                "all" => Some("rt_array_all"),
                _ => None,
            };
            if let Some(rt_name) = runtime_func {
                if rt_name == "rt_len" && compile_inline_len(ctx, builder, dest, args, false)? {
                    return Ok(());
                }
                let func_id = if let Some(&fid) = ctx.runtime_funcs.get(rt_name) {
                    Some(fid)
                } else {
                    // On-demand declaration: MIR referenced "str.starts_with" etc.
                    // but referenced_names only had the dotted form, not the rt_ name.
                    let call_conv = crate::codegen::shared::platform_call_conv();
                    let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
                    let param_count = args.len();
                    for _ in 0..param_count {
                        sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    }
                    sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    ctx.module
                        .declare_function(rt_name, cranelift_module::Linkage::Import, &sig)
                        .ok()
                        .map(|fid| {
                            ctx.func_ids.insert(rt_name.to_string(), fid);
                            fid
                        })
                };
                if let Some(func_id) = func_id {
                    let runtime_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    let arg_vals: Vec<_> = args.iter().map(|a| get_vreg_or_default(ctx, builder, a)).collect();
                    let arg_vals = adapt_args_to_signature(builder, runtime_ref, arg_vals);
                    let call = adapted_call(builder, runtime_ref, &arg_vals);
                    if let Some(d) = dest {
                        let results = builder.inst_results(call);
                        if !results.is_empty() {
                            ctx.vreg_values.insert(*d, results[0]);
                        }
                    }
                    return Ok(());
                }
            }
        }

        // Cross-module function: declare as import, resolve at link time.
        // Resolution order: 1) per-module use_map (from `use` statements),
        // 2) global import_map (unique names), 3) raw name fallback.
        let mut resolved_name = ctx
            .use_map
            .get(func_name)
            .or_else(|| ctx.import_map.get(func_name))
            .map(|s| s.as_str());

        // If not found and func_name contains '.', try additional name variants.
        // Prefer qualified/type-specific spellings before the bare method name;
        // otherwise common factory names like `create` can incorrectly bind to an
        // unrelated imported symbol from another type/module.
        let mut type_prefixed_storage;
        let mut dunder_storage;
        if resolved_name.is_none() {
            if let Some(dot_pos) = func_name.rfind('.') {
                let type_name = &func_name[..dot_pos];
                let method = &func_name[dot_pos + 1..];

                // Try: Type__method (double underscore variant)
                dunder_storage = format!("{}__{}", type_name, method);
                resolved_name = ctx
                    .use_map
                    .get(&dunder_storage)
                    .or_else(|| ctx.import_map.get(&dunder_storage))
                    .map(|s| s.as_str());

                // Try: lowercase_type_method (Simple convention)
                if resolved_name.is_none() {
                    type_prefixed_storage = format!("{}_{}", type_name.to_lowercase(), method);
                    resolved_name = ctx
                        .use_map
                        .get(&type_prefixed_storage)
                        .or_else(|| ctx.import_map.get(&type_prefixed_storage))
                        .map(|s| s.as_str());
                }

                // Last resort: bare method name
                if resolved_name.is_none() {
                    resolved_name = ctx
                        .use_map
                        .get(method)
                        .or_else(|| ctx.import_map.get(method))
                        .map(|s| s.as_str());
                }
            }
        }

        // Try: TypeName__method → typename_method (factory/constructor convention)
        // e.g., TreeSitter__new → treesitter_new
        if resolved_name.is_none() {
            if let Some((type_part, method_part)) = func_name.split_once("__") {
                if type_part.chars().next().is_some_and(|c| c.is_uppercase()) {
                    type_prefixed_storage = format!("{}_{}", type_part.to_lowercase(), method_part);
                    resolved_name = ctx
                        .use_map
                        .get(&type_prefixed_storage)
                        .or_else(|| ctx.import_map.get(&type_prefixed_storage))
                        .map(|s| s.as_str());
                }
            }
        }

        let has_resolved_name = resolved_name.is_some();
        let resolved_name = resolved_name.unwrap_or(func_name);

        // Sanitize symbol name: replace dots with _dot_ for linker compatibility.
        // Mach-O does not support dots in symbols; keeping this unconditional
        // ensures definition-side and reference-side names always match.
        let resolved_name = if resolved_name.contains('.') {
            std::borrow::Cow::Owned(resolved_name.replace('.', "_dot_"))
        } else {
            std::borrow::Cow::Borrowed(resolved_name)
        };

        let arg_vals: Vec<_> = args.iter().map(|a| get_vreg_or_default(ctx, builder, a)).collect();
        let arg_vals = reinterpret_float_bit_args(ctx, builder, args, arg_vals);
        // Strip spurious nil receiver from module-qualified free function calls.
        // HIR→MIR lowers `mod.func(args)` as [nil_receiver, args...]; when
        // fn_arities proves the callee expects fewer params, drop the leading nil.
        let arg_vals = if let Some(&arity) = ctx.fn_arities.get(resolved_name.as_ref()) {
            if arg_vals.len() > arity && arg_vals.len() == arity + 1 {
                arg_vals[1..].to_vec()
            } else {
                arg_vals
            }
        } else {
            arg_vals
        };
        if !has_resolved_name {
            if let Some((type_name, "new")) = func_name.rsplit_once('.') {
                if arg_vals.len() == 1 && type_name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                    if let Some(d) = dest {
                        ctx.vreg_values.insert(*d, arg_vals[0]);
                    }
                    return Ok(());
                }
            }
        }
        let func_id: Result<cranelift_module::FuncId, cranelift_module::ModuleError> = if let Some(&existing) =
            ctx.func_ids.get(resolved_name.as_ref())
        {
            Ok(existing)
        } else {
            if is_cross_module_data_export(ctx, func_name, resolved_name.as_ref()) {
                return Err(format!(
                    "cross-module call '{}' resolved to data/type export '{}'; expected a function. \
                     Constructor calls should lower to StructInit before codegen.",
                    func_name, resolved_name
                ));
            }
            let call_conv = crate::codegen::shared::platform_call_conv();
            let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
            let param_count = ctx
                .fn_arities
                .get(resolved_name.as_ref())
                .copied()
                .unwrap_or(arg_vals.len());
            for _ in 0..param_count {
                sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
            }
            sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
            match ctx
                .module
                .declare_function(&resolved_name, cranelift_module::Linkage::Import, &sig)
            {
                Ok(id) => {
                    ctx.func_ids.insert(resolved_name.to_string(), id);
                    Ok(id)
                }
                Err(_) => {
                    // Fallback: name may already be declared (e.g., imported impl method
                    // declared as Export via declare_functions). Use get_name to find it.
                    match ctx.module.get_name(&resolved_name) {
                        Some(cranelift_module::FuncOrDataId::Func(id)) => {
                            ctx.func_ids.insert(resolved_name.to_string(), id);
                            Ok(id)
                        }
                        Some(cranelift_module::FuncOrDataId::Data(_)) => {
                            return Err(format!(
                                "cross-module call '{}' resolved to data/type export '{}'; expected a function. \
                                 Constructor calls should lower to StructInit before codegen.",
                                func_name, resolved_name
                            ));
                        }
                        _ => {
                            if is_cross_module_data_export(ctx, func_name, resolved_name.as_ref()) {
                                return Err(format!(
                                    "cross-module call '{}' resolved to data/type export '{}'; expected a function. \
                                     Constructor calls should lower to StructInit before codegen.",
                                    func_name, resolved_name
                                ));
                            }
                            // Truly unresolved — return NIL
                            eprintln!("[CODEGEN-WARN] Failed to declare cross-module function '{}' (resolved: '{}'): IncompatibleDeclaration", func_name, resolved_name);
                            if let Some(d) = dest {
                                let nil = builder.ins().iconst(types::I64, 3);
                                ctx.vreg_values.insert(*d, nil);
                            }
                            return Ok(());
                        }
                    }
                }
            }
        };

        match func_id {
            Ok(func_id) => {
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                let adapted = adapt_args_to_signature(builder, func_ref, arg_vals);
                let call = adapted_call(builder, func_ref, &adapted);
                if let Some(d) = dest {
                    let results = builder.inst_results(call);
                    if !results.is_empty() {
                        ctx.vreg_values.insert(*d, results[0]);
                    }
                }
            }
            Err(e) => {
                eprintln!(
                    "[CODEGEN-WARN] Failed to declare cross-module function '{}' (resolved: '{}'): {}",
                    func_name, resolved_name, e
                );
                if let Some(d) = dest {
                    let nil = builder.ins().iconst(types::I64, 3);
                    ctx.vreg_values.insert(*d, nil);
                }
            }
        }
    }

    Ok(())
}
