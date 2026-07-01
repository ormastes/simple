//! Struct field access instruction compilation.
//!
//! Handles reading from and writing to struct fields via byte offsets.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags, TrapCode};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::types_util::type_id_to_cranelift;
use super::helpers::{call_runtime_2_void, create_string_constant, get_vreg_or_default};
use super::{InstrContext, InstrResult};

/// Guard a (possibly nil) struct receiver before a field load/store.
///
/// A `nil` receiver (e.g. `b: T? = nil; b.n`) masks to a null pointer;
/// dereferencing it is a wild segfault. A bare `trapz` lowers to `ud2`, which
/// aborts with a message-less SIGILL (exit 132, core dumped). The interpreter
/// reports a clean "field on nil" error, so the JIT prints a diagnostic to
/// stderr first, then traps — turning a silent crash into a named one.
fn guard_nonnull_receiver<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    obj_ptr: cranelift_codegen::ir::Value,
) -> InstrResult<()> {
    let err_block = builder.create_block();
    let ok_block = builder.create_block();
    // obj_ptr != 0 -> ok_block; nil (== 0) -> err_block.
    builder.ins().brif(obj_ptr, ok_block, &[], err_block, &[]);

    builder.switch_to_block(err_block);
    builder.seal_block(err_block);
    let (msg_ptr, msg_len) = create_string_constant(ctx, builder, "runtime error: field access on nil receiver")?;
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
    guard_nonnull_receiver(ctx, builder, obj_ptr)?;

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
    let load_ty = type_id_to_cranelift(field_type);
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
    _field_type: TypeId,
    value: VReg,
) -> InstrResult<()> {
    let obj_value = get_vreg_or_default(ctx, builder, &object);
    let tag_mask = builder.ins().iconst(types::I64, !0x7i64);
    let obj_ptr = builder.ins().band(obj_value, tag_mask);
    // Same null guard as FieldGet: storing into a `nil` receiver is a wild segfault.
    guard_nonnull_receiver(ctx, builder, obj_ptr)?;
    let val = get_vreg_or_default(ctx, builder, &value);
    builder.ins().store(MemFlags::new(), val, obj_ptr, byte_offset as i32);
    Ok(())
}
