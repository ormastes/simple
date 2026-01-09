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
    ParallelBackend, PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};

use super::shared::get_func_block_addr;
use super::types_util::{type_id_size, type_id_to_cranelift, type_to_cranelift};

// Declare submodules - no more include!
pub mod actors;
pub mod async_ops;
pub mod body;
pub mod closures_structs;
pub mod collections;
pub mod contracts;
pub mod core;
pub mod enum_union;
pub mod helpers;
pub mod memory;
pub mod methods;
pub mod parallel;
pub mod pattern;
pub mod pointers;
pub mod result;
pub mod simd_stubs;
pub mod units;

// Re-export key functions for backward compatibility
pub use body::compile_function_body;

// Import compile_* functions from submodules for use in compile_instruction
use actors::{
    compile_actor_join, compile_actor_recv, compile_actor_reply, compile_actor_send, compile_await,
    compile_generator_next,
};
use async_ops::{
    compile_actor_spawn, compile_future_create, compile_generator_create, compile_yield,
};
use closures_structs::{
    compile_closure_create, compile_indirect_call, compile_method_call_static,
    compile_method_call_virtual, compile_struct_init,
};
use collections::{
    compile_array_lit, compile_const_string, compile_dict_lit, compile_fstring_format,
    compile_gpu_atomic, compile_gpu_atomic_cmpxchg, compile_index_get, compile_index_set,
    compile_slice_op, compile_tuple_lit, compile_vec_blend, compile_vec_extract, compile_vec_lit,
    compile_vec_math, compile_vec_reduction, compile_vec_select, compile_vec_shuffle,
    compile_vec_with,
};
use contracts::compile_contract_check;
use core::{compile_binop, compile_builtin_io_call, compile_interp_call};
use enum_union::{
    compile_enum_discriminant, compile_enum_payload, compile_union_discriminant,
    compile_union_payload, compile_union_wrap,
};
use memory::{
    compile_gc_alloc, compile_get_element_ptr, compile_load, compile_local_addr, compile_store,
    compile_wait,
};
use methods::compile_builtin_method;
use parallel::{compile_par_filter, compile_par_for_each, compile_par_map, compile_par_reduce};
use pattern::{compile_enum_unit, compile_enum_with, compile_pattern_bind, compile_pattern_test};
use pointers::{compile_pointer_deref, compile_pointer_new, compile_pointer_ref};
use result::{
    compile_option_none, compile_option_some, compile_result_err, compile_result_ok,
    compile_try_unwrap,
};
use simd_stubs::{
    compile_neighbor_load, compile_vec_clamp, compile_vec_fma, compile_vec_gather,
    compile_vec_load, compile_vec_masked_load, compile_vec_masked_store, compile_vec_max_vec,
    compile_vec_min_vec, compile_vec_recip, compile_vec_scatter, compile_vec_store,
};
use units::{
    compile_unit_bound_check, compile_unit_narrow, compile_unit_saturate, compile_unit_widen,
};

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
    pub async_state_map: &'a Option<HashMap<BlockId, crate::mir::AsyncState>>,
}

/// Result type for instruction compilation - uses String errors for genericity
pub type InstrResult<T> = Result<T, String>;

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

        MirInst::Cast {
            dest,
            source,
            from_ty,
            to_ty,
        } => {
            let src_val = ctx.vreg_values[source];
            // Determine source and target types
            let is_from_float =
                *from_ty == crate::hir::TypeId::F64 || *from_ty == crate::hir::TypeId::F32;
            let is_to_float =
                *to_ty == crate::hir::TypeId::F64 || *to_ty == crate::hir::TypeId::F32;
            let is_to_i64 = *to_ty == crate::hir::TypeId::I64;

            let val = if is_from_float && !is_to_float {
                // Float to int conversion
                builder.ins().fcvt_to_sint(types::I64, src_val)
            } else if !is_from_float && is_to_float {
                // Int to float conversion
                builder.ins().fcvt_from_sint(types::F64, src_val)
            } else if is_from_float && is_to_float {
                // Float to float (F32 <-> F64)
                if *from_ty == crate::hir::TypeId::F32 {
                    builder.ins().fpromote(types::F64, src_val)
                } else {
                    builder.ins().fdemote(types::F32, src_val)
                }
            } else if is_to_i64 {
                // Int to i64 (no-op or sign extension)
                src_val
            } else {
                // Default: just copy the value
                src_val
            };
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::LocalAddr { dest, local_index } => {
            compile_local_addr(ctx, builder, *dest, *local_index)?;
        }

        MirInst::Load { dest, addr, .. } => {
            compile_load(ctx, builder, *dest, *addr)?;
        }

        MirInst::Store { addr, value, .. } => {
            compile_store(ctx, builder, *addr, *value)?;
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
            } else if let Some(&runtime_id) = ctx.runtime_funcs.get(func_name) {
                // Runtime FFI function
                let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
                let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
                let call = builder.ins().call(runtime_ref, &arg_vals);
                if let Some(d) = dest {
                    let results = builder.inst_results(call);
                    if !results.is_empty() {
                        ctx.vreg_values.insert(*d, results[0]);
                    }
                }
            }
        }

        MirInst::GetElementPtr { dest, base, index } => {
            compile_get_element_ptr(ctx, builder, *dest, *base, *index)?;
        }

        MirInst::GcAlloc { dest, ty } => {
            compile_gc_alloc(ctx, builder, *dest, *ty)?;
        }

        MirInst::Wait { dest, target } => {
            compile_wait(ctx, builder, *dest, *target)?;
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

        MirInst::VecSum { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_sum");
        }

        MirInst::VecProduct { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_product");
        }

        MirInst::VecMin { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_min");
        }

        MirInst::VecMax { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_max");
        }

        MirInst::VecAll { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_all");
        }

        MirInst::VecAny { dest, source } => {
            compile_vec_reduction(ctx, builder, *dest, *source, "rt_vec_any");
        }

        MirInst::VecExtract {
            dest,
            vector,
            index,
        } => {
            compile_vec_extract(ctx, builder, *dest, *vector, *index);
        }

        MirInst::VecWith {
            dest,
            vector,
            index,
            value,
        } => {
            compile_vec_with(ctx, builder, *dest, *vector, *index, *value);
        }

        MirInst::VecSqrt { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_sqrt");
        }

        MirInst::VecAbs { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_abs");
        }

        MirInst::VecFloor { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_floor");
        }

        MirInst::VecCeil { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_ceil");
        }

        MirInst::VecRound { dest, source } => {
            compile_vec_math(ctx, builder, *dest, *source, "rt_vec_round");
        }

        MirInst::VecShuffle {
            dest,
            source,
            indices,
        } => {
            compile_vec_shuffle(ctx, builder, *dest, *source, *indices);
        }

        MirInst::VecBlend {
            dest,
            first,
            second,
            indices,
        } => {
            compile_vec_blend(ctx, builder, *dest, *first, *second, *indices);
        }

        MirInst::VecSelect {
            dest,
            mask,
            if_true,
            if_false,
        } => {
            compile_vec_select(ctx, builder, *dest, *mask, *if_true, *if_false);
        }

        MirInst::GpuAtomic {
            dest,
            op,
            ptr,
            value,
        } => {
            compile_gpu_atomic(ctx, builder, *dest, *op, *ptr, *value);
        }

        MirInst::GpuAtomicCmpXchg {
            dest,
            ptr,
            expected,
            desired,
        } => {
            compile_gpu_atomic_cmpxchg(ctx, builder, *dest, *ptr, *expected, *desired);
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
            compile_enum_discriminant(ctx, builder, *dest, *value)?;
        }

        MirInst::EnumPayload { dest, value } => {
            compile_enum_payload(ctx, builder, *dest, *value)?;
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

        // Union type instructions - reuse enum runtime functions with type index
        MirInst::UnionDiscriminant { dest, value } => {
            compile_union_discriminant(ctx, builder, *dest, *value)?;
        }

        MirInst::UnionPayload {
            dest,
            value,
            type_index: _,
        } => {
            compile_union_payload(ctx, builder, *dest, *value)?;
        }

        MirInst::UnionWrap {
            dest,
            value,
            type_index,
        } => {
            compile_union_wrap(ctx, builder, *dest, *value, *type_index as u32)?;
        }

        MirInst::FutureCreate { dest, body_block } => {
            compile_future_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Await { dest, future } => {
            compile_await(ctx, builder, *dest, *future)?;
        }

        MirInst::ActorSpawn { dest, body_block } => {
            compile_actor_spawn(ctx, builder, *dest, *body_block);
        }

        MirInst::ActorSend { actor, message } => {
            compile_actor_send(ctx, builder, *actor, *message)?;
        }

        MirInst::ActorRecv { dest } => {
            compile_actor_recv(ctx, builder, *dest)?;
        }

        MirInst::ActorJoin { dest, actor } => {
            compile_actor_join(ctx, builder, *dest, *actor)?;
        }

        MirInst::ActorReply { message } => {
            compile_actor_reply(ctx, builder, *message)?;
        }

        MirInst::GeneratorCreate { dest, body_block } => {
            compile_generator_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Yield { value } => {
            return compile_yield(ctx, builder, *value);
        }

        MirInst::GeneratorNext { dest, generator } => {
            compile_generator_next(ctx, builder, *dest, *generator)?;
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
            compile_contract_check(
                ctx,
                builder,
                *condition,
                *kind,
                func_name,
                message.as_deref(),
            )?;
        }

        MirInst::ContractOldCapture { dest, value } => {
            // Simply copy the value to the destination register - captures happen at entry
            let val = ctx.vreg_values[value];
            ctx.vreg_values.insert(*dest, val);
        }

        // Coverage instrumentation probes - currently no-ops
        // Will be implemented when runtime coverage collection is added
        MirInst::DecisionProbe {
            result,
            decision_id,
            file,
            line,
            column,
        } => {
            // TODO: [codegen][P3] Call rt_decision_probe(decision_id, result)
            // For now, just ensure the result is used to prevent DCE
            let _ = ctx.vreg_values.get(result);
            let _ = (decision_id, file, line, column);
        }

        MirInst::ConditionProbe {
            decision_id,
            condition_id,
            result,
            file,
            line,
            column,
        } => {
            // TODO: [codegen][P3] Call rt_condition_probe(decision_id, condition_id, result)
            let _ = ctx.vreg_values.get(result);
            let _ = (decision_id, condition_id, file, line, column);
        }

        MirInst::PathProbe { path_id, block_id } => {
            // TODO: [codegen][P3] Call rt_path_probe(path_id, block_id)
            let _ = (path_id, block_id);
        }

        MirInst::UnitBoundCheck {
            value,
            unit_name,
            min,
            max,
            overflow,
        } => {
            compile_unit_bound_check(ctx, builder, *value, unit_name, *min, *max, *overflow)?;
        }

        MirInst::UnitWiden {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
        } => {
            compile_unit_widen(ctx, builder, *dest, *value, *from_bits, *to_bits, *signed)?;
        }

        MirInst::UnitNarrow {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
            overflow,
        } => {
            compile_unit_narrow(
                ctx, builder, *dest, *value, *from_bits, *to_bits, *signed, *overflow,
            )?;
        }

        MirInst::UnitSaturate {
            dest,
            value,
            min,
            max,
        } => {
            compile_unit_saturate(ctx, builder, *dest, *value, *min, *max)?;
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

        MirInst::PointerDeref {
            dest,
            pointer,
            kind,
        } => {
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

        MirInst::GpuSharedAlloc {
            dest,
            element_type,
            size,
        } => {
            super::instr_gpu::compile_gpu_shared_alloc(ctx, builder, *dest, *element_type, *size)?;
        }

        MirInst::NeighborLoad {
            dest,
            array,
            direction,
        } => {
            compile_neighbor_load(ctx, builder, *dest, *array, *direction)?;
        }

        // SIMD load/store operations
        MirInst::VecLoad {
            dest,
            array,
            offset,
        } => {
            compile_vec_load(ctx, builder, *dest, *array, *offset)?;
        }

        MirInst::VecStore {
            source,
            array,
            offset,
        } => {
            compile_vec_store(ctx, builder, *source, *array, *offset)?;
        }

        MirInst::VecGather {
            dest,
            array,
            indices,
        } => {
            compile_vec_gather(ctx, builder, *dest, *array, *indices)?;
        }

        MirInst::VecScatter {
            source,
            array,
            indices,
        } => {
            compile_vec_scatter(ctx, builder, *source, *array, *indices)?;
        }

        MirInst::VecFma { dest, a, b, c } => {
            compile_vec_fma(ctx, builder, *dest, *a, *b, *c)?;
        }

        MirInst::VecRecip { dest, source } => {
            compile_vec_recip(ctx, builder, *dest, *source)?;
        }

        MirInst::VecMaskedLoad {
            dest,
            array,
            offset,
            mask,
            default,
        } => {
            compile_vec_masked_load(ctx, builder, *dest, *array, *offset, *mask, *default)?;
        }

        MirInst::VecMaskedStore {
            source,
            array,
            offset,
            mask,
        } => {
            compile_vec_masked_store(ctx, builder, *source, *array, *offset, *mask)?;
        }

        MirInst::VecMinVec { dest, a, b } => {
            compile_vec_min_vec(ctx, builder, *dest, *a, *b)?;
        }

        MirInst::VecMaxVec { dest, a, b } => {
            compile_vec_max_vec(ctx, builder, *dest, *a, *b)?;
        }

        MirInst::VecClamp {
            dest,
            source,
            lo,
            hi,
        } => {
            compile_vec_clamp(ctx, builder, *dest, *source, *lo, *hi)?;
        }

        // Parallel iterator operations
        MirInst::ParMap {
            dest,
            input,
            closure,
            backend,
        } => {
            compile_par_map(ctx, builder, *dest, *input, *closure, *backend)?;
        }

        MirInst::ParReduce {
            dest,
            input,
            initial,
            closure,
            backend,
        } => {
            compile_par_reduce(ctx, builder, *dest, *input, *initial, *closure, *backend)?;
        }

        MirInst::ParFilter {
            dest,
            input,
            predicate,
            backend,
        } => {
            compile_par_filter(ctx, builder, *dest, *input, *predicate, *backend)?;
        }

        MirInst::ParForEach {
            input,
            closure,
            backend,
        } => {
            compile_par_for_each(ctx, builder, *input, *closure, *backend)?;
        }
    }
    Ok(())
}
