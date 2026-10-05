// Pointer operation instruction compilation.

use cranelift_codegen::ir::{InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::PointerKind;
use crate::mir::{MirInst, VReg};

use super::helpers::call_runtime_1;
use super::{InstrContext, InstrResult};

/// Compile a PointerNew instruction - allocate a pointer wrapping a value.
pub(crate) fn compile_pointer_new<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    kind: PointerKind,
    value: VReg,
) -> InstrResult<()> {
    let value_val = ctx.get_vreg(&value)?;

    // Select runtime function based on pointer kind
    let rt_func = match kind {
        PointerKind::Unique => "rt_unique_new",
        PointerKind::Shared => "rt_shared_new",
        PointerKind::Handle => "rt_handle_new",
        PointerKind::Weak => {
            // Weak pointers need a shared pointer to downgrade from
            // For now, create a shared pointer and downgrade it
            let shared_ptr = call_runtime_1(ctx, builder, "rt_shared_new", value_val);
            let result = call_runtime_1(ctx, builder, "rt_shared_downgrade", shared_ptr);
            ctx.vreg_values.insert(dest, result);
            return Ok(());
        }
        PointerKind::Borrow | PointerKind::BorrowMut => {
            // Borrow creation doesn't allocate - it just wraps the address
            // For now, pass through the value as-is (will be refined later)
            ctx.vreg_values.insert(dest, value_val);
            return Ok(());
        }
        PointerKind::RawConst | PointerKind::RawMut => {
            // SFFI raw pointers - pass through the address without wrapping
            // Used for extern function parameters
            ctx.vreg_values.insert(dest, value_val);
            return Ok(());
        }
    };

    let result = call_runtime_1(ctx, builder, rt_func, value_val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a PointerRef instruction - create a borrow reference.
pub(crate) fn compile_pointer_ref<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    kind: PointerKind,
    source: VReg,
) -> InstrResult<()> {
    let source_val = ctx.get_vreg(&source)?;
    // RawMut is emitted only for `&mut scalar_local` passed to an extern fn
    // (MIR `mark_extern_scalar_out_slots`): give the foreign side a real
    // address. `writeback_extern_out_slots` copies the slot back into the
    // local after the call.
    if kind == PointerKind::RawMut && ctx.vreg_from_local.contains_key(&source) {
        let slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            8,
            3,
        ));
        // The foreign side writes the DECLARED width (`bool*` writes one
        // byte), so zero the whole slot and store the value at that width.
        let slot_ty = out_slot_type(ctx, source);
        let zero = builder.ins().iconst(cranelift_codegen::ir::types::I64, 0);
        builder.ins().stack_store(zero, slot, 0);
        let stored = coerce_scalar(builder, source_val, slot_ty);
        builder.ins().stack_store(stored, slot, 0);
        let addr = builder.ins().stack_addr(cranelift_codegen::ir::types::I64, slot, 0);
        ctx.vreg_values.insert(dest, addr);
        return Ok(());
    }
    // Borrow references are currently passed through as the source value
    // In a full implementation, this would track borrow state at runtime
    ctx.vreg_values.insert(dest, source_val);
    Ok(())
}

/// Compile a PointerDeref instruction - dereference a pointer to get its value.
pub(crate) fn compile_pointer_deref<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    pointer: VReg,
    kind: PointerKind,
) -> InstrResult<()> {
    let ptr_val = ctx.get_vreg(&pointer)?;

    // Select runtime function based on pointer kind
    let rt_func = match kind {
        PointerKind::Unique => "rt_unique_get",
        PointerKind::Shared => "rt_shared_get",
        PointerKind::Handle => "rt_handle_get",
        PointerKind::Weak => {
            // Weak pointers need to be upgraded first
            let shared_ptr = call_runtime_1(ctx, builder, "rt_weak_upgrade", ptr_val);
            // Then get the value from the shared pointer
            let result = call_runtime_1(ctx, builder, "rt_shared_get", shared_ptr);
            ctx.vreg_values.insert(dest, result);
            return Ok(());
        }
        PointerKind::Borrow | PointerKind::BorrowMut => {
            // Borrows are currently transparent - just return the value
            ctx.vreg_values.insert(dest, ptr_val);
            return Ok(());
        }
        PointerKind::RawConst | PointerKind::RawMut => {
            // SFFI raw pointers - transparent dereference
            ctx.vreg_values.insert(dest, ptr_val);
            return Ok(());
        }
    };

    let result = call_runtime_1(ctx, builder, rt_func, ptr_val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// After an extern call, copy every RawMut out slot (see `compile_pointer_ref`)
/// that the call received back into the local it was taken from, so
/// `spl_dlopen_checked(path, &mut handle)` leaves the handle in `handle`.
pub(crate) fn writeback_extern_out_slots<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    args: &[VReg],
) {
    let Some(block) = ctx.func.blocks.iter().find(|b| b.id == ctx.mir_block_id) else {
        return;
    };
    let mut slots: Vec<(VReg, VReg)> = Vec::new();
    for inst in &block.instructions {
        if let MirInst::PointerRef {
            dest,
            kind: PointerKind::RawMut,
            source,
        } = inst
        {
            if args.contains(dest) {
                slots.push((*dest, *source));
            }
        }
    }
    for (ptr, source) in slots {
        let (Some(&local_index), Some(&addr)) = (ctx.vreg_from_local.get(&source), ctx.vreg_values.get(&ptr)) else {
            continue;
        };
        let var = ctx
            .variables
            .get(&local_index)
            .or_else(|| ctx.extra_variables.get(&local_index))
            .copied();
        let Some(var) = var else {
            continue;
        };
        let slot_ty = out_slot_type(ctx, source);
        let written = builder.ins().load(slot_ty, MemFlags::trusted(), addr, 0);
        // def_var must match the Variable's declared type, which is the type
        // `use_var` hands back.
        let var_ty = {
            let current = builder.use_var(var);
            builder.func.dfg.value_type(current)
        };
        let updated = coerce_scalar(builder, written, var_ty);
        builder.def_var(var, updated);
        ctx.vreg_values.insert(source, updated);
    }
}

/// Width the foreign side writes through a `*mut T` out slot for `T`.
fn out_slot_type<M: Module>(ctx: &InstrContext<'_, M>, source: VReg) -> cranelift_codegen::ir::Type {
    ctx.vreg_types
        .get(&source)
        .copied()
        .map(super::super::types_util::type_id_to_cranelift)
        .unwrap_or(cranelift_codegen::ir::types::I64)
}

/// Convert a scalar between Cranelift widths: integers resize (zero-extend;
/// out slots carry the raw foreign bit pattern), floats promote/demote, and an
/// i64 holding f64 bits becomes a float by bitcast.
fn coerce_scalar(
    builder: &mut FunctionBuilder,
    value: cranelift_codegen::ir::Value,
    to: cranelift_codegen::ir::Type,
) -> cranelift_codegen::ir::Value {
    use cranelift_codegen::ir::types;
    let from = builder.func.dfg.value_type(value);
    if from == to {
        return value;
    }
    if from.is_int() && to.is_int() {
        return if from.bits() > to.bits() {
            builder.ins().ireduce(to, value)
        } else {
            builder.ins().uextend(to, value)
        };
    }
    if from.is_float() && to.is_float() {
        return if from.bits() < to.bits() {
            builder.ins().fpromote(to, value)
        } else {
            builder.ins().fdemote(to, value)
        };
    }
    if from == types::I64 && to.is_float() {
        let wide = builder.ins().bitcast(types::F64, MemFlags::new(), value);
        return if to == types::F32 { builder.ins().fdemote(types::F32, wide) } else { wide };
    }
    if from.is_float() && to == types::I64 {
        let wide = if from == types::F32 { builder.ins().fpromote(types::F64, value) } else { value };
        return builder.ins().bitcast(types::I64, MemFlags::new(), wide);
    }
    value
}
