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
    let cranelift_ty = type_id_to_cranelift(field_type);
    let val = builder
        .ins()
        .load(cranelift_ty, MemFlags::new(), obj_ptr, byte_offset as i32);
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
