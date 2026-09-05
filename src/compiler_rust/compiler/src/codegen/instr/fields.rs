//! Struct field access instruction compilation.
//!
//! Handles reading from and writing to struct fields via byte offsets.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags, TrapCode};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::types_util::type_id_to_cranelift;
use super::helpers::{call_runtime_2_void, call_runtime_3, create_string_constant, get_vreg_or_default};
use super::{InstrContext, InstrResult};

/// Guard a struct receiver before a field load/store without dereferencing it.
///
/// A `nil` receiver (e.g. `b: T? = nil; b.n`) masks to a null pointer;
/// dereferencing it is a wild segfault. A bare `trapz` lowers to `ud2`, which
/// aborts with a message-less SIGILL (exit 132, core dumped). The interpreter
/// reports a clean "field on nil" error, so the JIT prints a diagnostic to
/// stderr first, then traps — turning a silent crash into a named one.
fn guard_nonnull_receiver<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    receiver: cranelift_codegen::ir::Value,
    byte_offset: usize,
    access_width: usize,
) -> InstrResult<()> {
    // LOCAL BUILD NEUTRALIZATION (not committed): the receiver guard calls
    // rt_struct_receiver_valid, which lives only in runtime_native.c — a TU
    // the seed crate cannot link (duplicate rt_host_gpu_* symbols). Until the
    // guard lane lands the seed-side symbol, emit no guard so the JIT keeps
    // the pre-guard behavior. Revert via /tmp/fields_rs_guarded.rs.
    if std::env::var("SIMPLE_SEED_FIELD_GUARD").is_err() {
        return Ok(());
    }
    let err_block = builder.create_block();
    let ok_block = builder.create_block();
    let offset = builder.ins().iconst(types::I64, byte_offset as i64);
    let width = builder.ins().iconst(types::I64, access_width as i64);
    let valid = call_runtime_3(ctx, builder, "rt_struct_receiver_valid", receiver, offset, width);
    builder.ins().brif(valid, ok_block, &[], err_block, &[]);

    builder.switch_to_block(err_block);
    builder.seal_block(err_block);
    let (msg_ptr, msg_len) = create_string_constant(ctx, builder, "runtime error: invalid field receiver")?;
    call_runtime_2_void(ctx, builder, "rt_eprintln_str", msg_ptr, msg_len);
    builder.ins().trap(TrapCode::unwrap_user(12));

    builder.switch_to_block(ok_block);
    builder.seal_block(ok_block);
    Ok(())
}

/// Compile FieldGet instruction: loads a field value from a struct
pub fn compile_field_get<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    object: VReg,
    byte_offset: usize,
    field_type: TypeId,
) -> InstrResult<()> {
    let obj_value = get_vreg_or_default(ctx, builder, &object);
    let tag_mask = builder.ins().iconst(types::I64, !0x7i64);
    let obj_ptr = builder.ins().band(obj_value, tag_mask);

    // Field access on a `nil` receiver (e.g. `b: T? = nil; b.n`) masks to a null
    // pointer; loading from it is a wild segfault. Print a clean diagnostic and
    // trap instead of either a silent SIGSEGV or a message-less SIGILL.
    let load_ty = type_id_to_cranelift(field_type);
    guard_nonnull_receiver(ctx, builder, obj_value, byte_offset, load_ty.bytes() as usize)?;

    // Diagnostic: log FieldGet at non-zero offsets when tracing is enabled.
    // This helps diagnose cross-module FieldGet bugs where byte_offset is
    // computed incorrectly due to type falling back to ANY.
    if std::env::var("SIMPLE_TRACE_FIELD_GET").is_ok() {
        eprintln!(
            "[TRACE FieldGet] dest={:?} object={:?} byte_offset={} field_type={:?} func={}",
            dest, object, byte_offset, field_type, ctx.func.name
        );
    }

    // Field slots are 8-byte aligned, but each slot stores the field's native
    // representation. Loading with a fixed I64 type corrupts native f32/f64
    // fields and mis-types smaller integer fields for downstream dispatch.
    let val = builder
        .ins()
        .load(load_ty, MemFlags::new(), obj_ptr, byte_offset as i32);
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile FieldSet instruction: stores a value into a struct field
pub fn compile_field_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    object: VReg,
    byte_offset: usize,
    field_type: TypeId,
    value: VReg,
) -> InstrResult<()> {
    let obj_value = get_vreg_or_default(ctx, builder, &object);
    let tag_mask = builder.ins().iconst(types::I64, !0x7i64);
    let obj_ptr = builder.ins().band(obj_value, tag_mask);
    // Same null guard as FieldGet: storing into a `nil` receiver is a wild segfault.
    let store_width = type_id_to_cranelift(field_type).bytes() as usize;
    guard_nonnull_receiver(ctx, builder, obj_value, byte_offset, store_width)?;
    let val = get_vreg_or_default(ctx, builder, &value);
    if std::env::var("SIMPLE_TRACE_FIELD_GET").is_ok() {
        eprintln!(
            "[TRACE FieldSet] object={:?} byte_offset={} field_type={:?} val_ty={:?} func={}",
            object,
            byte_offset,
            field_type,
            builder.func.dfg.value_type(val),
            ctx.func.name
        );
    }
    let val = coerce_to_field_type(builder, val, type_id_to_cranelift(field_type));
    builder.ins().store(MemFlags::new(), val, obj_ptr, byte_offset as i32);
    Ok(())
}

/// Narrow/widen a value to the field slot's native type before storing it.
///
/// `compile_field_get` loads each field with `type_id_to_cranelift(field_type)`,
/// i.e. the field's DECLARED width. The store side used to write whatever type
/// the source vreg happened to carry, so an `f32` field written from an f64
/// literal stored 8 bytes of f64 and the 4-byte F32 load read back only the
/// low half of the f64 bit pattern: `2.5f64` is `0x4004000000000000`, whose
/// low 32 bits are zero, so `s.a` read back as `0.0`; `0.1f64` read back as
/// `-1.588e-23`. Float stores are demoted/promoted (a value conversion, not a
/// bit truncation) and integer stores are narrowed, so the store width always
/// matches the load width.
fn coerce_to_field_type(
    builder: &mut FunctionBuilder,
    val: cranelift_codegen::ir::Value,
    want: cranelift_codegen::ir::Type,
) -> cranelift_codegen::ir::Value {
    let have = builder.func.dfg.value_type(val);
    if have == want {
        return val;
    }
    if have.is_float() && want.is_float() {
        return if want.bits() < have.bits() {
            builder.ins().fdemote(want, val)
        } else {
            builder.ins().fpromote(want, val)
        };
    }
    // Integer field slots narrower than the incoming value would otherwise
    // store past the slot and be read back truncated at a different width.
    if have.is_int() && want.is_int() && want.bits() < have.bits() {
        return builder.ins().ireduce(want, val);
    }
    val
}
