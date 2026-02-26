// Pointer operation instruction compilation.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::PointerKind;
use crate::mir::VReg;

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
            let shared_id = ctx.runtime_funcs["rt_shared_new"];
            let shared_ref = ctx.module.declare_func_in_func(shared_id, builder.func);
            let shared_call = builder.ins().call(shared_ref, &[value_val]);
            let shared_ptr = builder.inst_results(shared_call)[0];

            let weak_id = ctx.runtime_funcs["rt_shared_downgrade"];
            let weak_ref = ctx.module.declare_func_in_func(weak_id, builder.func);
            let weak_call = builder.ins().call(weak_ref, &[shared_ptr]);
            let result = builder.inst_results(weak_call)[0];
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

    let func_id = ctx.runtime_funcs[rt_func];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[value_val]);
    let result = builder.inst_results(call)[0];
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
            let upgrade_id = ctx.runtime_funcs["rt_weak_upgrade"];
            let upgrade_ref = ctx.module.declare_func_in_func(upgrade_id, builder.func);
            let upgrade_call = builder.ins().call(upgrade_ref, &[ptr_val]);
            let shared_ptr = builder.inst_results(upgrade_call)[0];

            // Then get the value from the shared pointer
            let get_id = ctx.runtime_funcs["rt_shared_get"];
            let get_ref = ctx.module.declare_func_in_func(get_id, builder.func);
            let get_call = builder.ins().call(get_ref, &[shared_ptr]);
            let result = builder.inst_results(get_call)[0];
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

    let func_id = ctx.runtime_funcs[rt_func];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[ptr_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}
