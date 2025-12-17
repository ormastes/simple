//! Unified instruction compilation for both AOT (cranelift.rs) and JIT (jit.rs) backends.
//!
//! This module provides instruction compilation that works with any Cranelift Module type,
//! eliminating the duplication between cranelift_instr.rs and jit_instr.rs.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;

use crate::hir::{BinOp, PointerKind, TypeId, UnaryOp};
use crate::mir::{
    BindingStep, BlockId, ContractKind, FStringPart, MirFunction, MirInst, MirLiteral, MirPattern,
    PatternBinding, Terminator, VReg,
};

use super::shared::get_func_block_addr;
use super::types_util::{type_id_size, type_id_to_cranelift, type_to_cranelift};

// Include split modules for better organization
include!("instr_methods.rs");
include!("instr_async.rs");
include!("instr_result.rs");
include!("instr_pattern.rs");
include!("instr_collections.rs");
include!("instr_core.rs");
include!("instr_closures_structs.rs");
include!("instr_body.rs");

/// Context for instruction compilation, holding all state needed to compile MIR instructions.
pub struct InstrContext<'a, M: Module> {
    pub module: &'a mut M,
    pub func_ids: &'a HashMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: &'a HashMap<&'static str, cranelift_module::FuncId>,
    pub vreg_values: &'a mut HashMap<VReg, cranelift_codegen::ir::Value>,
    pub local_addr_map: &'a mut HashMap<VReg, usize>,
    pub variables: &'a HashMap<usize, cranelift_frontend::Variable>,
    pub func: &'a MirFunction,
    pub entry_block: cranelift_codegen::ir::Block,
    pub blocks: &'a HashMap<BlockId, cranelift_codegen::ir::Block>,
    pub mir_block_id: BlockId,
    pub generator_state_map: &'a Option<HashMap<BlockId, crate::mir::GeneratorState>>,
}

/// Result type for instruction compilation - uses String errors for genericity
pub type InstrResult<T> = Result<T, String>;

/// Helper to create a string constant in module data and return (ptr, len) values
fn create_string_constant<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    text: &str,
) -> InstrResult<(cranelift_codegen::ir::Value, cranelift_codegen::ir::Value)> {
    let bytes = text.as_bytes();
    let data_id = ctx
        .module
        .declare_anonymous_data(true, false)
        .map_err(|e| e.to_string())?;
    let mut data_desc = cranelift_module::DataDescription::new();
    data_desc.define(bytes.to_vec().into_boxed_slice());
    ctx.module
        .define_data(data_id, &data_desc)
        .map_err(|e| e.to_string())?;

    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let ptr = builder.ins().global_value(types::I64, global_val);
    let len = builder.ins().iconst(types::I64, bytes.len() as i64);
    
    Ok((ptr, len))
}

/// Helper to perform indirect call with result handling
fn indirect_call_with_result<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    sig_ref: cranelift_codegen::ir::SigRef,
    fn_ptr: cranelift_codegen::ir::Value,
    call_args: &[cranelift_codegen::ir::Value],
    dest: &Option<VReg>,
) {
    let call = builder.ins().call_indirect(sig_ref, fn_ptr, call_args);

    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            let null = builder.ins().iconst(types::I64, 0);
            ctx.vreg_values.insert(*d, null);
        }
    }
}

/// Compile a single MIR instruction.
pub fn compile_instruction<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    inst: &MirInst,
) -> InstrResult<()> {
    match inst {
        MirInst::ConstInt { dest, value } => {
            let val = builder.ins().iconst(types::I64, *value);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::ConstFloat { dest, value } => {
            let val = builder.ins().f64const(*value);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::ConstBool { dest, value } => {
            let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::Copy { dest, src } => {
            let val = ctx.vreg_values[src];
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::BinOp {
            dest,
            op,
            left,
            right,
        } => {
            let lhs = ctx.vreg_values[left];
            let rhs = ctx.vreg_values[right];
            let val = compile_binop(ctx, builder, *op, lhs, rhs)?;
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::LocalAddr { dest, local_index } => {
            let addr_val = builder.ins().iconst(types::I64, *local_index as i64);
            ctx.vreg_values.insert(*dest, addr_val);
            ctx.local_addr_map.insert(*dest, *local_index);
        }

        MirInst::Load { dest, addr, .. } => {
            if let Some(&local_index) = ctx.local_addr_map.get(addr) {
                if let Some(&var) = ctx.variables.get(&local_index) {
                    let val = builder.use_var(var);
                    ctx.vreg_values.insert(*dest, val);
                }
            } else {
                let val = ctx.vreg_values[addr];
                ctx.vreg_values.insert(*dest, val);
            }
        }

        MirInst::Store { addr, value, .. } => {
            if let Some(&local_index) = ctx.local_addr_map.get(addr) {
                if let Some(&var) = ctx.variables.get(&local_index) {
                    let val = ctx.vreg_values[value];
                    builder.def_var(var, val);
                }
            }
        }

        MirInst::UnaryOp { dest, op, operand } => {
            let val = ctx.vreg_values[operand];
            let result = match op {
                UnaryOp::Neg => builder.ins().ineg(val),
                UnaryOp::Not => {
                    builder
                        .ins()
                        .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::Equal, val, 0)
                }
                UnaryOp::BitNot => builder.ins().bnot(val),
            };
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::Call { dest, target, args } => {
            let func_name = target.name();

            // Check if this is a built-in I/O function (print, println, etc.)
            if let Some(result) = compile_builtin_io_call(ctx, builder, func_name, args, dest)? {
                if let Some(d) = dest {
                    ctx.vreg_values.insert(*d, result);
                }
            } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
                // User-defined function
                let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
                let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
                let call = builder.ins().call(callee_ref, &arg_vals);
                if let Some(d) = dest {
                    let results = builder.inst_results(call);
                    if !results.is_empty() {
                        ctx.vreg_values.insert(*d, results[0]);
                    }
                }
            }
        }

        MirInst::GetElementPtr { dest, base, index } => {
            let base_val = ctx.vreg_values[base];
            let index_val = ctx.vreg_values[index];
            let element_size = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(index_val, element_size);
            let addr = builder.ins().iadd(base_val, offset);
            ctx.vreg_values.insert(*dest, addr);
        }

        MirInst::GcAlloc { dest, ty } => {
            let alloc_id = ctx.runtime_funcs["rt_alloc"];
            let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
            let size = type_id_size(*ty) as i64;
            let size_val = builder.ins().iconst(types::I64, size.max(8));
            let call = builder.ins().call(alloc_ref, &[size_val]);
            let ptr = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, ptr);
        }

        MirInst::Wait { dest, target } => {
            let wait_id = ctx.runtime_funcs["rt_wait"];
            let wait_ref = ctx.module.declare_func_in_func(wait_id, builder.func);
            let target_val = ctx.vreg_values[target];
            let call = builder.ins().call(wait_ref, &[target_val]);
            let result = builder.inst_results(call)[0];
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
            }
        }

        MirInst::InterpCall {
            dest,
            func_name,
            args,
        } => {
            compile_interp_call(ctx, builder, dest, func_name, args)?;
        }

        MirInst::InterpEval { dest, expr_index } => {
            let interp_eval_id = ctx.runtime_funcs["rt_interp_eval"];
            let interp_eval_ref = ctx
                .module
                .declare_func_in_func(interp_eval_id, builder.func);
            let idx = builder.ins().iconst(types::I64, *expr_index as i64);
            let call = builder.ins().call(interp_eval_ref, &[idx]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::ArrayLit { dest, elements } => {
            compile_array_lit(ctx, builder, *dest, elements);
        }

        MirInst::TupleLit { dest, elements } => {
            compile_tuple_lit(ctx, builder, *dest, elements);
        }

        MirInst::VecLit { dest, elements } => {
            compile_vec_lit(ctx, builder, *dest, elements);
        }

        MirInst::DictLit { dest, keys, values } => {
            compile_dict_lit(ctx, builder, *dest, keys, values);
        }

        MirInst::IndexGet {
            dest,
            collection,
            index,
        } => {
            compile_index_get(ctx, builder, *dest, *collection, *index);
        }

        MirInst::IndexSet {
            collection,
            index,
            value,
        } => {
            compile_index_set(ctx, builder, *collection, *index, *value);
        }

        MirInst::SliceOp {
            dest,
            collection,
            start,
            end,
            step,
        } => {
            compile_slice_op(ctx, builder, *dest, *collection, *start, *end, *step);
        }

        MirInst::Spread { dest, source } => {
            let source_val = ctx.vreg_values[source];
            ctx.vreg_values.insert(*dest, source_val);
        }

        MirInst::ConstString { dest, value } => {
            compile_const_string(ctx, builder, *dest, value);
        }

        MirInst::ConstSymbol { dest, value } => {
            let hash = value.bytes().enumerate().fold(0i64, |acc, (i, b)| {
                acc.wrapping_add((b as i64).wrapping_mul(31i64.wrapping_pow(i as u32)))
            });
            let symbol_val = builder.ins().iconst(types::I64, hash | (1i64 << 62));
            ctx.vreg_values.insert(*dest, symbol_val);
        }

        MirInst::FStringFormat { dest, parts } => {
            compile_fstring_format(ctx, builder, *dest, parts);
        }

        MirInst::ClosureCreate {
            dest,
            func_name,
            closure_size,
            capture_offsets,
            capture_types: _,
            captures,
        } => {
            compile_closure_create(
                ctx,
                builder,
                *dest,
                func_name,
                *closure_size as usize,
                capture_offsets,
                captures,
            );
        }

        MirInst::IndirectCall {
            dest,
            callee,
            param_types,
            return_type,
            args,
            effect: _,
        } => {
            compile_indirect_call(ctx, builder, dest, *callee, param_types, *return_type, args);
        }

        MirInst::StructInit {
            dest,
            type_id: _,
            struct_size,
            field_offsets,
            field_types,
            field_values,
        } => {
            compile_struct_init(
                ctx,
                builder,
                *dest,
                *struct_size as usize,
                field_offsets,
                field_types,
                field_values,
            );
        }

        MirInst::FieldGet {
            dest,
            object,
            byte_offset,
            field_type,
        } => {
            let obj_ptr = ctx.vreg_values[object];
            let cranelift_ty = type_id_to_cranelift(*field_type);
            let val =
                builder
                    .ins()
                    .load(cranelift_ty, MemFlags::new(), obj_ptr, *byte_offset as i32);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::FieldSet {
            object,
            byte_offset,
            field_type: _,
            value,
        } => {
            let obj_ptr = ctx.vreg_values[object];
            let val = ctx.vreg_values[value];
            builder
                .ins()
                .store(MemFlags::new(), val, obj_ptr, *byte_offset as i32);
        }

        MirInst::MethodCallStatic {
            dest,
            receiver,
            func_name,
            args,
        } => {
            compile_method_call_static(ctx, builder, dest, *receiver, func_name, args)?;
        }

        MirInst::MethodCallVirtual {
            dest,
            receiver,
            vtable_slot,
            param_types,
            return_type,
            args,
        } => {
            compile_method_call_virtual(
                ctx,
                builder,
                dest,
                *receiver,
                *vtable_slot as usize,
                param_types,
                *return_type,
                args,
            );
        }

        MirInst::BuiltinMethod {
            dest,
            receiver,
            receiver_type,
            method,
            args,
        } => {
            compile_builtin_method(ctx, builder, dest, *receiver, receiver_type, method, args)?;
        }

        MirInst::PatternTest {
            dest,
            subject,
            pattern,
        } => {
            compile_pattern_test(ctx, builder, *dest, *subject, pattern);
        }

        MirInst::PatternBind {
            dest,
            subject,
            binding,
        } => {
            compile_pattern_bind(ctx, builder, *dest, *subject, binding);
        }

        MirInst::EnumDiscriminant { dest, value } => {
            let disc_id = ctx.runtime_funcs["rt_enum_discriminant"];
            let disc_ref = ctx.module.declare_func_in_func(disc_id, builder.func);
            let val = ctx.vreg_values[value];
            let call = builder.ins().call(disc_ref, &[val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::EnumPayload { dest, value } => {
            let payload_id = ctx.runtime_funcs["rt_enum_payload"];
            let payload_ref = ctx.module.declare_func_in_func(payload_id, builder.func);
            let val = ctx.vreg_values[value];
            let call = builder.ins().call(payload_ref, &[val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::EnumUnit {
            dest,
            enum_name: _,
            variant_name,
        } => {
            compile_enum_unit(ctx, builder, *dest, variant_name);
        }

        MirInst::EnumWith {
            dest,
            enum_name: _,
            variant_name,
            payload,
        } => {
            compile_enum_with(ctx, builder, *dest, variant_name, *payload);
        }

        MirInst::FutureCreate { dest, body_block } => {
            compile_future_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Await { dest, future } => {
            let await_id = ctx.runtime_funcs["rt_future_await"];
            let await_ref = ctx.module.declare_func_in_func(await_id, builder.func);
            let future_val = ctx.vreg_values[future];
            let call = builder.ins().call(await_ref, &[future_val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::ActorSpawn { dest, body_block } => {
            compile_actor_spawn(ctx, builder, *dest, *body_block);
        }

        MirInst::ActorSend { actor, message } => {
            let send_id = ctx.runtime_funcs["rt_actor_send"];
            let send_ref = ctx.module.declare_func_in_func(send_id, builder.func);
            let actor_val = ctx.vreg_values[actor];
            let msg_val = ctx.vreg_values[message];
            builder.ins().call(send_ref, &[actor_val, msg_val]);
        }

        MirInst::ActorRecv { dest } => {
            let recv_id = ctx.runtime_funcs["rt_actor_recv"];
            let recv_ref = ctx.module.declare_func_in_func(recv_id, builder.func);
            let call = builder.ins().call(recv_ref, &[]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::GeneratorCreate { dest, body_block } => {
            compile_generator_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Yield { value } => {
            return compile_yield(ctx, builder, *value);
        }

        MirInst::GeneratorNext { dest, generator } => {
            let next_id = ctx.runtime_funcs["rt_generator_next"];
            let next_ref = ctx.module.declare_func_in_func(next_id, builder.func);
            let gen_val = ctx.vreg_values[generator];
            let call = builder.ins().call(next_ref, &[gen_val]);
            let result = builder.inst_results(call)[0];

            // The runtime returns a tagged RuntimeValue; unwrap to a raw i64 for
            // downstream arithmetic in codegen paths.
            let unwrap_id = ctx.runtime_funcs["rt_value_as_int"];
            let unwrap_ref = ctx.module.declare_func_in_func(unwrap_id, builder.func);
            let unwrap_call = builder.ins().call(unwrap_ref, &[result]);
            let unwrapped = builder.inst_results(unwrap_call)[0];
            ctx.vreg_values.insert(*dest, unwrapped);
        }

        MirInst::TryUnwrap {
            dest,
            value,
            error_block,
            error_dest,
        } => {
            compile_try_unwrap(ctx, builder, *dest, *value, *error_block, *error_dest);
        }

        MirInst::OptionSome { dest, value } => {
            compile_option_some(ctx, builder, *dest, *value);
        }

        MirInst::OptionNone { dest } => {
            compile_option_none(ctx, builder, *dest);
        }

        MirInst::ResultOk { dest, value } => {
            compile_result_ok(ctx, builder, *dest, *value);
        }

        MirInst::ResultErr { dest, value } => {
            compile_result_err(ctx, builder, *dest, *value);
        }

        MirInst::ContractCheck {
            condition,
            kind,
            func_name,
            message,
        } => {
            compile_contract_check(ctx, builder, *condition, *kind, func_name, message.as_deref())?;
        }

        MirInst::ContractOldCapture { dest, value } => {
            // Simply copy the value to the destination register - captures happen at entry
            let val = ctx.vreg_values[value];
            ctx.vreg_values.insert(*dest, val);
        }

        // =========================================================================
        // Pointer instructions
        // =========================================================================
        MirInst::PointerNew { dest, kind, value } => {
            compile_pointer_new(ctx, builder, *dest, *kind, *value)?;
        }

        MirInst::PointerRef { dest, kind, source } => {
            compile_pointer_ref(ctx, builder, *dest, *kind, *source)?;
        }

        MirInst::PointerDeref { dest, pointer, kind } => {
            compile_pointer_deref(ctx, builder, *dest, *pointer, *kind)?;
        }

        // =========================================================================
        // GPU instructions
        // =========================================================================
        MirInst::GpuGlobalId { dest, dim } => {
            super::instr_gpu::compile_gpu_global_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuLocalId { dest, dim } => {
            super::instr_gpu::compile_gpu_local_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuGroupId { dest, dim } => {
            super::instr_gpu::compile_gpu_group_id(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuGlobalSize { dest, dim } => {
            super::instr_gpu::compile_gpu_global_size(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuLocalSize { dest, dim } => {
            super::instr_gpu::compile_gpu_local_size(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuNumGroups { dest, dim } => {
            super::instr_gpu::compile_gpu_num_groups(ctx, builder, *dest, *dim)?;
        }

        MirInst::GpuBarrier => {
            super::instr_gpu::compile_gpu_barrier(ctx, builder)?;
        }

        MirInst::GpuMemFence { scope } => {
            super::instr_gpu::compile_gpu_mem_fence(ctx, builder, *scope)?;
        }

        MirInst::GpuAtomic { dest, op, addr, value, expected } => {
            super::instr_gpu::compile_gpu_atomic(ctx, builder, *dest, *op, *addr, *value, *expected)?;
        }

        MirInst::GpuSharedAlloc { dest, element_type, size } => {
            super::instr_gpu::compile_gpu_shared_alloc(ctx, builder, *dest, *element_type, *size)?;
        }

        MirInst::NeighborLoad { dest, array, direction } => {
            // Stub for SIMD neighbor load - in real GPU codegen this would
            // compute (this.index() +/- 1) and load from array at that index
            let _ = (array, direction);
            let zero = builder.ins().iconst(types::I64, 0);
            ctx.vreg_values.insert(*dest, zero);
        }
    }
    Ok(())
}

/// Compile a contract check instruction.
/// This checks the condition and calls a runtime function to panic if it fails.
fn compile_contract_check<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    condition: VReg,
    kind: ContractKind,
    func_name: &str,
    _message: Option<&str>,
) -> InstrResult<()> {
    let cond = ctx.vreg_values[&condition];

    // Get the kind as an integer for the runtime call
    let kind_val = match kind {
        ContractKind::Precondition => 0i64,
        ContractKind::Postcondition => 1i64,
        ContractKind::ErrorPostcondition => 2i64,
        ContractKind::InvariantEntry => 3i64,
        ContractKind::InvariantExit => 4i64,
    };

    // Check if we have the runtime contract check function
    if let Some(&func_id) = ctx.runtime_funcs.get("simple_contract_check") {
        // Call runtime: simple_contract_check(condition: bool, kind: i64, func_name_ptr: *const u8, func_name_len: i64)
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

        // Create string data for function name and get (ptr, len) values
        let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

        // Convert bool condition to i64 for the call
        let cond_i64 = builder.ins().uextend(types::I64, cond);
        let kind_iconst = builder.ins().iconst(types::I64, kind_val);

        builder.ins().call(func_ref, &[cond_i64, kind_iconst, name_ptr, name_len]);
    } else {
        // Fallback: generate inline check with trap on failure
        // Create a conditional branch that traps if the condition is false
        let trap_block = builder.create_block();
        let continue_block = builder.create_block();

        // Branch based on condition
        builder.ins().brif(cond, continue_block, &[], trap_block, &[]);

        // Trap block - triggers a panic
        builder.switch_to_block(trap_block);
        builder.seal_block(trap_block);
        builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(kind_val as u8));

        // Continue block - normal execution
        builder.switch_to_block(continue_block);
        builder.seal_block(continue_block);
    }
    Ok(())
}

// =============================================================================
// Pointer Operations
// =============================================================================

/// Compile a PointerNew instruction - allocate a pointer wrapping a value.
fn compile_pointer_new<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    kind: PointerKind,
    value: VReg,
) -> InstrResult<()> {
    let value_val = ctx.vreg_values[&value];

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
    };

    let func_id = ctx.runtime_funcs[rt_func];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[value_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a PointerRef instruction - create a borrow reference.
fn compile_pointer_ref<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    _builder: &mut FunctionBuilder,
    dest: VReg,
    _kind: PointerKind,
    source: VReg,
) -> InstrResult<()> {
    // Borrow references are currently passed through as the source value
    // In a full implementation, this would track borrow state at runtime
    let source_val = ctx.vreg_values[&source];
    ctx.vreg_values.insert(dest, source_val);
    Ok(())
}

/// Compile a PointerDeref instruction - dereference a pointer to get its value.
fn compile_pointer_deref<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    pointer: VReg,
    kind: PointerKind,
) -> InstrResult<()> {
    let ptr_val = ctx.vreg_values[&pointer];

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
    };

    let func_id = ctx.runtime_funcs[rt_func];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let call = builder.ins().call(func_ref, &[ptr_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
    Ok(())
}

