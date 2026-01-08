// Closure and struct initialization helpers.

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::VReg;

use super::{InstrContext, InstrResult};
use super::helpers::{create_string_constant, indirect_call_with_result};
use super::super::types_util::type_id_to_cranelift;

fn compile_closure_create<M: Module>(
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
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let closure_ptr = builder.inst_results(call)[0];

    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let fn_addr = builder.ins().func_addr(types::I64, func_ref);
        builder
            .ins()
            .store(MemFlags::new(), fn_addr, closure_ptr, 0);
    } else {
        let null = builder.ins().iconst(types::I64, 0);
        builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
    }

    for (i, offset) in capture_offsets.iter().enumerate() {
        let cap_val = ctx.vreg_values[&captures[i]];
        builder
            .ins()
            .store(MemFlags::new(), cap_val, closure_ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, closure_ptr);
}

fn compile_indirect_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    callee: VReg,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let closure_ptr = ctx.vreg_values[&callee];
    let fn_ptr = builder
        .ins()
        .load(types::I64, MemFlags::new(), closure_ptr, 0);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params
            .push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns
            .push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![closure_ptr];
    for arg in args {
        call_args.push(ctx.vreg_values[arg]);
    }

    indirect_call_with_result(ctx, builder, sig_ref, fn_ptr, &call_args, dest);
}

fn compile_struct_init<M: Module>(
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
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let ptr = builder.inst_results(call)[0];

    for (i, (offset, field_type)) in field_offsets.iter().zip(field_types.iter()).enumerate() {
        let field_val = ctx.vreg_values[&field_values[i]];
        let _cranelift_ty = type_id_to_cranelift(*field_type);
        builder
            .ins()
            .store(MemFlags::new(), field_val, ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, ptr);
}

fn compile_method_call_static<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    func_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let mut call_args = vec![ctx.vreg_values[&receiver]];
        for arg in args {
            call_args.push(ctx.vreg_values[arg]);
        }
        let call = builder.ins().call(func_ref, &call_args);
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
        let call = builder.ins().call(not_found_ref, &[name_ptr, name_len]);

        if let Some(d) = dest {
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*d, result);
        }
    }
    Ok(())
}

fn compile_method_call_virtual<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    vtable_slot: usize,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let recv_ptr = ctx.vreg_values[&receiver];
    let vtable_ptr = builder.ins().load(types::I64, MemFlags::new(), recv_ptr, 0);
    let slot_offset = (vtable_slot as i32) * 8;
    let method_ptr = builder
        .ins()
        .load(types::I64, MemFlags::new(), vtable_ptr, slot_offset);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params
            .push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns
            .push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![recv_ptr];
    for arg in args {
        call_args.push(ctx.vreg_values[arg]);
    }

    indirect_call_with_result(ctx, builder, sig_ref, method_ptr, &call_args, dest);
}
