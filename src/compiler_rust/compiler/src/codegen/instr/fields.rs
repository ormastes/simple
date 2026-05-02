//! Struct field access instruction compilation.
//!
//! Handles reading from and writing to struct fields via byte offsets.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::super::types_util::type_id_to_cranelift;
use super::helpers::get_vreg_or_default;
use super::{InstrContext, InstrResult};

/// Compile FieldGet instruction: loads a field value from a struct
pub fn compile_field_get<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    object: VReg,
    byte_offset: usize,
    field_type: TypeId,
) -> InstrResult<()> {
    let obj_ptr = get_vreg_or_default(ctx, builder, &object);

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
    let obj_ptr = get_vreg_or_default(ctx, builder, &object);
    let val = get_vreg_or_default(ctx, builder, &value);
    builder.ins().store(MemFlags::new(), val, obj_ptr, byte_offset as i32);
    Ok(())
}
