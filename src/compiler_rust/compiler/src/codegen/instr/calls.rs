//! Function call instruction compilation.
//!
//! Handles all forms of function calls: user-defined, runtime FFI, and built-in functions.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, InstBuilder, MemFlags, Value};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::codegen::runtime_ffi::RUNTIME_FUNCS;
use crate::hir::TypeId;
use crate::mir::{CallTarget, VReg};

use super::core::{compile_builtin_io_call, vreg_is_signed};
use super::helpers::{
    adapted_call, call_runtime_3, create_cstring_constant, get_vreg_or_default, inline_runtime_array_len_value,
    inline_runtime_len_value,
};
use super::{InstrContext, InstrResult};

/// Check if a function name is a profiler function (to avoid recursive instrumentation)
fn is_profiler_function(name: &str) -> bool {
    name.starts_with("rt_profiler_")
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
    if trusted_array {
        let byte_ptr = builder.ins().iadd(data_ptr, normalized_index);
        let packed_byte = builder.ins().load(types::I8, MemFlags::new(), byte_ptr, 0);
        let packed_value = builder.ins().uextend(types::I64, packed_byte);
        builder.ins().jump(done_block, &[packed_value]);
        builder.seal_block(load_block);

        builder.switch_to_block(done_block);
        let result = builder.block_params(done_block)[0];
        builder.seal_block(done_block);
        ctx.vreg_values.insert(*dest, result);
        return Ok(true);
    }

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
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };

    let load_block = builder.create_block();
    let byte_block = builder.create_block();
    let word_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

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

    builder.switch_to_block(load_block);
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
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };

    let load_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

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

    builder.switch_to_block(load_block);
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
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };

    let store_block = builder.create_block();
    let byte_block = builder.create_block();
    let word_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

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

    builder.switch_to_block(store_block);
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
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);
    let len = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 8);
    let data_ptr = builder.ins().load(types::I64, MemFlags::new(), ptr_bits, 24);
    let index_is_unsigned = vreg_is_signed(ctx, args[1]) == Some(false);
    let normalized_index = if index_is_unsigned {
        index
    } else {
        let negative = builder.ins().icmp(IntCC::SignedLessThan, index, zero);
        let from_end = builder.ins().iadd(len, index);
        builder.ins().select(negative, from_end, index)
    };

    let store_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

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

    builder.switch_to_block(store_block);
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
) -> InstrResult<bool> {
    if args.len() != 2 {
        return Ok(false);
    }
    let Some(dest) = dest else {
        return Ok(false);
    };

    let array = coerce_vreg_to_i64(ctx, builder, args[0]);
    let xor_value = coerce_vreg_to_i64(ctx, builder, args[1]);
    let zero = builder.ins().iconst(types::I64, 0);
    let min_heap_value = builder.ins().iconst(types::I64, 4096);
    let ptr_mask = builder.ins().iconst(types::I64, !7i64);
    let ptr_bits = builder.ins().band(array, ptr_mask);

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

    let too_small = builder.ins().icmp(IntCC::SignedLessThan, array, min_heap_value);
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

    builder.switch_to_block(loop_block);
    let sum0 = builder.block_params(loop_block)[0];
    let sum1 = builder.block_params(loop_block)[1];
    let sum2 = builder.block_params(loop_block)[2];
    let sum3 = builder.block_params(loop_block)[3];
    let idx = builder.block_params(loop_block)[4];
    let cursor = builder.block_params(loop_block)[5];
    let idx_plus_seven = builder.ins().iadd_imm(idx, 7);
    let has_chunk = builder.ins().icmp(IntCC::SignedLessThan, idx_plus_seven, length);
    builder.ins().brif(
        has_chunk,
        chunk_block,
        &[],
        tail_block,
        &[sum0, sum1, sum2, sum3, idx, cursor],
    );

    builder.switch_to_block(chunk_block);
    let xor_vec = builder.ins().splat(types::I64X2, xor_value);
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
    let idx_plus_seven = builder.ins().iadd_imm(idx, 7);
    let has_chunk = builder.ins().icmp(IntCC::SignedLessThan, idx_plus_seven, length);
    let second_test_block = builder.create_block();
    builder.ins().brif(
        has_chunk,
        second_test_block,
        &[],
        tail_block,
        &[sum0, sum1, sum2, sum3, idx, cursor],
    );
    builder.seal_block(chunk_second_block);

    builder.switch_to_block(second_test_block);
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
    builder.seal_block(second_test_block);
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
    let shifted = builder.ins().ishl_imm(tail_sum, 3);
    builder.ins().brif(
        has_tail,
        tail_scalar_block,
        &[tail_sum, tail_idx, tail_cursor],
        done_block,
        &[shifted],
    );

    builder.switch_to_block(tail_scalar_block);
    let tail_sum = builder.block_params(tail_scalar_block)[0];
    let tail_idx = builder.block_params(tail_scalar_block)[1];
    let tail_cursor = builder.block_params(tail_scalar_block)[2];
    let has_tail = builder.ins().icmp(IntCC::SignedLessThan, tail_idx, length);
    let shifted = builder.ins().ishl_imm(tail_sum, 3);
    builder
        .ins()
        .brif(has_tail, tail_body_block, &[], done_block, &[shifted]);

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
    let index = coerce_vreg_to_i64(ctx, builder, args[1]);
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
    let len = coerce_vreg_to_i64(ctx, builder, args[1]);
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
    let value = coerce_vreg_to_i64(ctx, builder, args[2]);
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
#[allow(dead_code)] // reason: reachable via FFI or future entry point; not yet wired
fn untag_runtime_value_to_int(
    builder: &mut FunctionBuilder,
    value: cranelift_codegen::ir::Value,
) -> cranelift_codegen::ir::Value {
    let three = builder.ins().iconst(types::I64, 3);
    builder.ins().sshr(value, three)
}

/// Returns which Simple-level argument indices are text parameters for a given
/// runtime FFI function. Text arguments are RuntimeValue strings that must be
/// expanded to (ptr, len) pairs when calling the C-ABI FFI function.
///
/// For example, `rt_process_run(cmd, args)` has text at index 0: the `cmd`
/// RuntimeValue string must be expanded to `(cmd_ptr, cmd_len)` before calling
/// the Rust FFI function `rt_process_run(cmd_ptr, cmd_len, args)`.
pub fn text_arg_indices(func_name: &str) -> Option<&'static [usize]> {
    match func_name {
        // Print/IO (text → ptr, len)
        "rt_print_str" | "rt_println_str" | "rt_eprint_str" | "rt_eprintln_str" => Some(&[0]),

        // Environment variables
        "rt_env_get" | "rt_env_get_i64" | "rt_get_env" | "rt_env_exists" | "rt_env_remove" => Some(&[0]),
        "rt_env_set" | "rt_set_env" => Some(&[0, 1]),

        // File I/O (single path)
        "rt_file_exists"
        | "rt_file_canonicalize"
        | "rt_file_read_text"
        | "rt_file_size"
        | "rt_file_hash_sha256"
        | "rt_file_fsync"
        | "rt_file_fsync_cached"
        | "rt_file_delete"
        | "rt_file_remove"
        | "rt_file_read_lines"
        | "rt_file_read_bytes"
        | "rt_file_mmap_read_text"
        | "rt_file_mmap_len"
        | "rt_file_mmap_read_bytes" => Some(&[0]),
        // File I/O (two text params: path + content, or src + dest)
        "rt_file_write_text"
        | "rt_file_copy"
        | "rt_file_rename"
        | "rt_file_append_text"
        | "rt_file_write_bytes"
        | "rt_file_move" => Some(&[0, 1]),

        // Directory operations
        "rt_dir_create" | "rt_dir_create_all" | "rt_dir_list" | "rt_dir_remove" | "rt_dir_remove_all"
        | "rt_dir_glob" | "rt_dir_walk" | "rt_set_current_dir" => Some(&[0]),
        "rt_file_find" => Some(&[0, 1]),

        // Async I/O driver text arguments
        "rt_driver_submit_open" => Some(&[1]),
        "rt_driver_submit_connect" | "rt_driver_submit_send" | "rt_driver_submit_write" => Some(&[2]),

        // Path operations (single path)
        "rt_path_basename" | "rt_path_dirname" | "rt_path_ext" | "rt_path_absolute" | "rt_path_stem" => Some(&[0]),
        // Path operations (two paths)
        "rt_path_relative" | "rt_path_join" => Some(&[0, 1]),

        // Process execution (cmd is text, args is RuntimeValue array)
        "rt_process_run" | "rt_process_spawn" | "rt_process_execute" => Some(&[0]),
        "rt_process_run_timeout" => Some(&[0]),

        // Contract checking (func_name is text at different positions)
        "simple_contract_check" => Some(&[2]),
        "simple_contract_check_msg" => Some(&[2, 3]),
        "rt_contract_violation_new" => Some(&[1, 2]),

        // Interpreter bridge
        "rt_interp_call" => Some(&[0]),

        // FFI object system (method name at index 1)
        "rt_ffi_call_method" | "rt_ffi_has_method" | "rt_ffi_object_call_method" | "rt_ffi_object_has_method" => {
            Some(&[1])
        }
        "rt_ffi_type_register" => Some(&[0]),

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
        "ffi_regex_is_match" | "ffi_regex_find" | "ffi_regex_find_all" | "ffi_regex_captures" | "ffi_regex_split" => {
            Some(&[0, 1])
        }
        "ffi_regex_replace" | "ffi_regex_replace_all" => Some(&[0, 1, 2]),
        "ffi_regex_split_n" => Some(&[0, 1]),

        // Cranelift self-hosting
        "rt_cranelift_new_module" | "rt_cranelift_new_aot_module" => Some(&[0]),
        "rt_cranelift_begin_function" => Some(&[1]),
        "rt_cranelift_get_function_ptr" => Some(&[1]),

        // File stat (path is text, rest are output pointers)
        "rt_file_stat" => Some(&[0]),

        // Hosted compositor (Cocoa / Win32 windows take title text at index 2)
        "rt_cocoa_window_new" | "rt_win32_window_new" => Some(&[2]),

        _ => None,
    }
}

/// Expand text RuntimeValue arguments to (ptr, len) pairs for FFI calls.
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
                // preserves legacy unsigned-widen default for runtime/FFI
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
    // For runtime FFI matching only, strip module prefix to find the base function name.
    // e.g., "compiler__driver__driver_types__rt_file_read_text" → "rt_file_read_text"
    let func_name_for_ffi = func_name_raw
        .rsplit_once("__")
        .map(|(_, tail)| tail)
        .unwrap_or(func_name_raw);
    // Map Simple builtin names to runtime FFI function names (for FFI lookup only)
    // Note: "str", "int", "input" are handled in compile_builtin_io_call, not here
    let ffi_name: &str = match func_name_for_ffi {
        "sys_get_args" => "rt_get_args",
        "sys_exit" => "rt_exit",
        "rt_file_read_text" => "rt_file_read_text_rv",
        "rt_file_delete" => "rt_file_remove",
        "rt_println" => "rt_println_value",
        "rt_print" => "rt_print_value",
        "len" => "rt_len",
        other => other,
    };
    // Use raw name for user-function lookups (func_ids, use_map, import_map)
    // but mapped FFI name for runtime_funcs and builtin I/O checks
    let func_name: &str = func_name_raw;

    // Handle Result/Option constructor builtins (Ok, Err, Some, None)
    // Also handle qualified names like "MyResult::Ok", "Option::None", etc.
    let variant_name = func_name
        .rsplit_once("::")
        .or_else(|| func_name.rsplit_once('.'))
        .map(|(_, v)| v)
        .unwrap_or(func_name);
    if matches!(variant_name, "Ok" | "Err" | "Some" | "None") {
        if let Some(d) = dest {
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
                // Empty payload uses tagged nil (3), not raw 0
                builder.ins().iconst(types::I64, 3)
            };
            let result = call_runtime_3(ctx, builder, "rt_enum_new", enum_id_val, disc_val, payload_val);
            ctx.vreg_values.insert(*d, result);
        }
        return Ok(());
    }

    if compile_simple_runtime_memory_intrinsic(ctx, builder, dest, func_name_for_ffi, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_data_ptr" && compile_inline_array_data_ptr(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_header_ptr" && compile_inline_array_header_ptr(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_get" && compile_inline_array_get(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_get_text" && compile_inline_array_get_word(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_set" && compile_inline_array_set(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_array_set_text" && compile_inline_array_set_word(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_numeric_xor_sum_u64" && compile_inline_numeric_xor_sum_u64(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_numeric_contains_u64_data"
        && compile_inline_numeric_contains_u64(ctx, builder, dest, args, true)?
    {
        return Ok(());
    }
    if ffi_name == "rt_numeric_contains_u64" && compile_inline_numeric_contains_u64(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if matches!(ffi_name, "rt_array_set_len_known" | "rt_array_set_len_known_text")
        && compile_inline_array_set_len_known(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if matches!(ffi_name, "rt_len" | "rt_array_len")
        && compile_inline_len(ctx, builder, dest, args, ffi_name == "rt_array_len")?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u8_at" && compile_inline_bytes_u8_at(ctx, builder, dest, args, true)? {
        return Ok(());
    }
    if ffi_name == "rt_bytes_u8_at" && compile_inline_bytes_u8_at(ctx, builder, dest, args, false)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u32_le_at" && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u64_le_at" && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u32_le_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u64_le_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u8_unchecked"
        && compile_inline_typed_bytes_le_unchecked(ctx, builder, dest, args, 1)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u8_data_at" && compile_inline_typed_bytes_data_at(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_at" && compile_inline_typed_words_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_at" && compile_inline_typed_words_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_unchecked" && compile_inline_typed_words_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_unchecked" && compile_inline_typed_words_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_data_at" && compile_inline_typed_words_data_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_data_at" && compile_inline_typed_words_data_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_data_at_checked"
        && compile_inline_typed_words_data_at_checked(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_raw_data_at" && compile_inline_typed_words_raw_data_at(ctx, builder, dest, args)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_set" && compile_inline_typed_words_u32_set(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_push" && compile_inline_typed_words_push(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_push" && compile_inline_typed_words_push(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_push_known_at"
        && compile_inline_typed_words_push_known_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_push_known_at"
        && compile_inline_typed_words_push_known_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_push_known_data_at"
        && compile_inline_typed_words_push_known_data_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_push_known_data_at"
        && compile_inline_typed_words_push_known_data_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u32_store_known_data_at"
        && compile_inline_typed_words_store_known_data_at(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_words_u64_store_known_data_at"
        && compile_inline_typed_words_store_known_data_at(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u8_push" && compile_inline_typed_bytes_u8_push(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "_adler_reduce" && compile_inline_adler_reduce(ctx, builder, dest, args)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u32_le_set"
        && compile_inline_typed_bytes_le_set_unchecked(ctx, builder, dest, args, 4)?
    {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u64_le_set"
        && compile_inline_typed_bytes_le_set_unchecked(ctx, builder, dest, args, 8)?
    {
        return Ok(());
    }
    if ffi_name == "rt_bytes_u32_le_at" && compile_inline_bytes_le_at(ctx, builder, dest, args, 4)? {
        return Ok(());
    }
    if ffi_name == "rt_bytes_u64_le_at" && compile_inline_bytes_le_at(ctx, builder, dest, args, 8)? {
        return Ok(());
    }
    if ffi_name == "rt_typed_bytes_u8_set" && compile_inline_bytes_u8_set(ctx, builder, dest, args, true)? {
        return Ok(());
    }
    if ffi_name == "rt_bytes_u8_set" && compile_inline_bytes_u8_set(ctx, builder, dest, args, false)? {
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
    // Use ffi_name for builtin/runtime checks since these match on short names
    if let Some(result) = compile_builtin_io_call(ctx, builder, ffi_name, args, dest)? {
        if let Some(d) = dest {
            ctx.vreg_values.insert(*d, result);
        }
    } else if let Some(&runtime_id) = ctx.runtime_funcs.get(ffi_name) {
        // Runtime FFI function — checked BEFORE func_ids because runtime functions
        // are also registered in func_ids for name resolution. Checking here first
        // ensures text expansion and FFI-specific handling (tagging, return type
        // extension) is always applied for known runtime functions.
        if !is_profiler_function(ffi_name) {
            emit_profiler_call(ctx, builder, ffi_name)?;
        }
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);

        // Check if this function needs RuntimeValue tagging for certain arguments
        let tagging_indices = needs_runtime_value_tagging(ffi_name);
        // Check if this function returns RuntimeValue that needs untagging
        let needs_untagging = needs_runtime_value_untagging(ffi_name);

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

        // Expand text RuntimeValue arguments to (ptr, len) pairs for C-ABI FFI calls.
        // This handles the ABI mismatch between Simple (everything is RuntimeValue i64)
        // and Rust FFI (text is decomposed into *const u8 + usize).
        let arg_vals = if let Some(text_indices) = text_arg_indices(ffi_name) {
            expand_text_args(ctx, builder, &arg_vals, text_indices)
        } else {
            arg_vals
        };

        let arg_vals = adapt_args_to_signature(builder, runtime_ref, arg_vals);
        let call = adapted_call(builder, runtime_ref, &arg_vals);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                let mut result = results[0];

                // Extend smaller return types to i64 (the standard vreg type)
                // This is needed because some FFI functions return i32 (e.g., rt_exec)
                // but all vregs are expected to be i64.
                //
                // FR-DRIVER-0002b: if the destination VReg is declared signed,
                // use `sextend` so negative runtime-returned narrow values keep
                // their sign. Unsigned and unknown destinations keep the old
                // `uextend` (zero-extend) behavior — this preserves Rust-FFI
                // contracts where values like `u32 = 0xFFFFFFFF` must not
                // sign-extend to `-1` when consumed as `i64`.
                let dest_signed = super::core::vreg_is_signed(ctx, *d) == Some(true);
                if let Some(ret_type) = get_runtime_return_type(ffi_name) {
                    if ret_type == types::I32 || ret_type == types::I8 {
                        result = if dest_signed {
                            builder.ins().sextend(types::I64, result)
                        } else {
                            builder.ins().uextend(types::I64, result)
                        };
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
        if !is_profiler_function(ffi_name) {
            emit_profiler_return(ctx, builder)?;
        }
    } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
        // User-defined function (not a known runtime FFI function)
        if !is_profiler_function(func_name) {
            emit_profiler_call(ctx, builder, func_name)?;
        }
        let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
        let arg_vals: Vec<_> = args.iter().map(|a| get_vreg_or_default(ctx, builder, a)).collect();
        let arg_vals = adapt_args_to_signature(builder, callee_ref, arg_vals);
        let call = adapted_call(builder, callee_ref, &arg_vals);
        if !is_profiler_function(func_name) {
            emit_profiler_return(ctx, builder)?;
        }
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    } else {
        // Before falling through to cross-module import, check if this is a qualified
        // builtin method call like "ALPHA_LOWER.contains" or "items.push".
        // The parser sometimes treats `val.method(args)` as a qualified function call
        // when it can't resolve the receiver type. Map the method part to the
        // corresponding runtime function.
        if let Some(dot_pos) = func_name.rfind('.') {
            let method_part = &func_name[dot_pos + 1..];
            let runtime_func: Option<&str> = match method_part {
                "contains" | "contains_key" | "has_key" => Some("rt_contains"),
                "len" => Some("rt_len"),
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
                "split" => Some("rt_string_split"),
                "replace" => Some("rt_string_replace"),
                "to_upper" | "upper" => Some("rt_string_to_upper"),
                "to_lower" | "lower" => Some("rt_string_to_lower"),
                "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
                "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
                "index_of" | "find" | "find_str" => Some("rt_string_find"),
                "rfind" | "last_index_of" => Some("rt_string_rfind"),
                "to_string" | "str" => Some("rt_to_string"),
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
                if let Some(&func_id) = ctx.runtime_funcs.get(rt_name) {
                    // The first argument to the runtime call is the receiver (the part before the dot).
                    // For a Call instruction, the receiver was lowered as the first arg by MIR.
                    // However, for qualified calls like `X.method(args)`, there may be no
                    // explicit receiver arg — re-check by looking at whether the receiver is
                    // a known global.  In practice the MIR lowering wraps these as
                    // Call { target: "X.method", args } with no implicit receiver, so we pass
                    // args as-is (the runtime function expects receiver + method args).
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
            let call_conv = crate::codegen::shared::platform_call_conv();
            let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
            for _ in 0..arg_vals.len() {
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
                        _ => {
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
