// Pointer operation instruction compilation.

use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::PointerKind;
use crate::mir::VReg;

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
            // FFI raw pointers - pass through the address without wrapping
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
    _builder: &mut FunctionBuilder,
    dest: VReg,
    _kind: PointerKind,
    source: VReg,
) -> InstrResult<()> {
    // Borrow references are currently passed through as the source value
    // In a full implementation, this would track borrow state at runtime
    let source_val = ctx.get_vreg(&source)?;
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
            // FFI raw pointers - transparent dereference
            ctx.vreg_values.insert(dest, ptr_val);
            return Ok(());
        }
    };

    let result = call_runtime_1(ctx, builder, rt_func, ptr_val);
    ctx.vreg_values.insert(dest, result);
    Ok(())
}
