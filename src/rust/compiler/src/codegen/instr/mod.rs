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
    BindingStep, BlockId, ContractKind, FStringPart, MirFunction, MirInst, MirLiteral, MirPattern, ParallelBackend,
    PatternBinding, Terminator, UnitOverflowBehavior, VReg,
};

use super::shared::get_func_block_addr;
use super::types_util::{type_id_size, type_id_to_cranelift, type_to_cranelift};

// Declare submodules
pub mod actors;
pub mod async_ops;
pub mod basic_ops;
pub mod body;
pub mod calls;
pub mod closures_structs;
pub mod collections;
pub mod constants;
pub mod contracts;
pub mod core;
pub mod coverage;
pub mod enum_union;
pub mod extern_classes;
pub mod fields;
pub mod helpers;
pub mod interpreter;
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
use async_ops::{compile_actor_spawn, compile_future_create, compile_generator_create, compile_yield};
use basic_ops::{compile_cast, compile_copy, compile_spread, compile_unary_op};
use calls::compile_call;
use closures_structs::{
    compile_closure_create, compile_indirect_call, compile_method_call_static, compile_method_call_virtual,
    compile_struct_init,
};
use collections::{
    compile_array_lit, compile_const_string, compile_dict_lit, compile_fstring_format, compile_gpu_atomic,
    compile_gpu_atomic_cmpxchg, compile_index_get, compile_index_set, compile_slice_op, compile_tuple_lit,
    compile_vec_blend, compile_vec_extract, compile_vec_lit, compile_vec_math, compile_vec_reduction,
    compile_vec_select, compile_vec_shuffle, compile_vec_with,
};
use constants::{compile_const_bool, compile_const_float, compile_const_int, compile_const_symbol};
use contracts::compile_contract_check;
use core::{compile_binop, compile_builtin_io_call, compile_interp_call};
use coverage::{compile_condition_probe, compile_decision_probe, compile_path_probe};
use enum_union::{
    compile_enum_discriminant, compile_enum_payload, compile_union_discriminant, compile_union_payload,
    compile_union_wrap,
};
use extern_classes::compile_extern_method_call;
use fields::{compile_field_get, compile_field_set};
use interpreter::{compile_contract_old_capture, compile_interp_eval};
use memory::{compile_gc_alloc, compile_get_element_ptr, compile_load, compile_local_addr, compile_store, compile_wait};
use methods::compile_builtin_method;
use parallel::{compile_par_filter, compile_par_for_each, compile_par_map, compile_par_reduce};
use pattern::{compile_enum_unit, compile_enum_with, compile_pattern_bind, compile_pattern_test};
use pointers::{compile_pointer_deref, compile_pointer_new, compile_pointer_ref};
use result::{compile_option_none, compile_option_some, compile_result_err, compile_result_ok, compile_try_unwrap};
use simd_stubs::{
    compile_neighbor_load, compile_vec_clamp, compile_vec_fma, compile_vec_gather, compile_vec_load,
    compile_vec_masked_load, compile_vec_masked_store, compile_vec_max_vec, compile_vec_min_vec, compile_vec_recip,
    compile_vec_scatter, compile_vec_store,
};
use units::{compile_unit_bound_check, compile_unit_narrow, compile_unit_saturate, compile_unit_widen};

/// Context for instruction compilation, holding all state needed to compile MIR instructions.
pub struct InstrContext<'a, M: Module> {
    pub module: &'a mut M,
    pub func_ids: &'a HashMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: &'a HashMap<&'static str, cranelift_module::FuncId>,
    pub global_ids: &'a HashMap<String, cranelift_module::DataId>,
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
            compile_const_int(ctx, builder, *dest, *value)?;
        }

        MirInst::ConstFloat { dest, value } => {
            compile_const_float(ctx, builder, *dest, *value)?;
        }

        MirInst::ConstBool { dest, value } => {
            compile_const_bool(ctx, builder, *dest, *value)?;
        }

        MirInst::Copy { dest, src } => {
            compile_copy(ctx, builder, *dest, *src)?;
        }

        MirInst::BinOp { dest, op, left, right } => {
            let lhs = ctx.vreg_values.get(left).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG BinOp] Missing lhs VReg {:?}, using default 0", left);
                builder.ins().iconst(types::I64, 0)
            });
            let rhs = ctx.vreg_values.get(right).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG BinOp] Missing rhs VReg {:?}, using default 0", right);
                builder.ins().iconst(types::I64, 0)
            });
            let val = compile_binop(ctx, builder, *op, lhs, rhs)?;
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::Cast {
            dest,
            source,
            from_ty,
            to_ty,
        } => {
            compile_cast(ctx, builder, *dest, *source, *from_ty, *to_ty)?;
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

        MirInst::GlobalLoad { dest, global_name, ty } => {
            let global_id = ctx.global_ids.get(global_name)
                .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
            let global_ref = ctx.module.declare_data_in_func(*global_id, builder.func);
            let global_addr = builder.ins().global_value(types::I64, global_ref);
            let val = builder.ins().load(type_id_to_cranelift(*ty), MemFlags::new(), global_addr, 0);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::GlobalStore { global_name, value, ty } => {
            let global_id = ctx.global_ids.get(global_name)
                .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
            let global_ref = ctx.module.declare_data_in_func(*global_id, builder.func);
            let global_addr = builder.ins().global_value(types::I64, global_ref);
            let val = ctx.vreg_values.get(value)
                .ok_or_else(|| format!("GlobalStore: vreg {:?} not found", value))?;
            builder.ins().store(MemFlags::new(), *val, global_addr, 0);
        }

        MirInst::UnaryOp { dest, op, operand } => {
            compile_unary_op(ctx, builder, *dest, *op, *operand)?;
        }

        MirInst::Call { dest, target, args } => {
            compile_call(ctx, builder, dest, target, args)?;
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

        MirInst::InterpCall { dest, func_name, args } => {
            compile_interp_call(ctx, builder, dest, func_name, args)?;
        }

        MirInst::InterpEval { dest, expr_index } => {
            compile_interp_eval(ctx, builder, *dest, *expr_index as usize)?;
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

        MirInst::VecExtract { dest, vector, index } => {
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

        MirInst::VecShuffle { dest, source, indices } => {
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

        MirInst::GpuAtomic { dest, op, ptr, value } => {
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
            compile_spread(ctx, builder, *dest, *source)?;
        }

        MirInst::ConstString { dest, value } => {
            compile_const_string(ctx, builder, *dest, value);
        }

        MirInst::ConstSymbol { dest, value } => {
            compile_const_symbol(ctx, builder, *dest, value)?;
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
            compile_field_get(ctx, builder, *dest, *object, *byte_offset as usize, *field_type)?;
        }

        MirInst::FieldSet {
            object,
            byte_offset,
            field_type,
            value,
        } => {
            compile_field_set(ctx, builder, *object, *byte_offset as usize, *field_type, *value)?;
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

        MirInst::ExternMethodCall {
            dest,
            receiver,
            class_name,
            method_name,
            is_static,
            args,
        } => {
            compile_extern_method_call(
                ctx,
                builder,
                dest,
                receiver.as_ref().copied(),
                class_name,
                method_name,
                *is_static,
                args,
            )?;
        }

        MirInst::PatternTest { dest, subject, pattern } => {
            compile_pattern_test(ctx, builder, *dest, *subject, pattern);
        }

        MirInst::PatternBind { dest, subject, binding } => {
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
            compile_contract_check(ctx, builder, *condition, *kind, func_name, message.as_deref())?;
        }

        MirInst::ContractOldCapture { dest, value } => {
            compile_contract_old_capture(ctx, builder, *dest, *value)?;
        }

        // Coverage instrumentation probes
        MirInst::DecisionProbe {
            result,
            decision_id,
            file,
            line,
            column,
        } => {
            compile_decision_probe(ctx, builder, *result, *decision_id, file, *line, *column)?;
        }

        MirInst::ConditionProbe {
            decision_id,
            condition_id,
            result,
            file,
            line,
            column,
        } => {
            compile_condition_probe(ctx, builder, *decision_id, *condition_id, *result, file, *line, *column)?;
        }

        MirInst::PathProbe { path_id, block_id } => {
            compile_path_probe(ctx, builder, *path_id, *block_id)?;
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
            compile_unit_narrow(ctx, builder, *dest, *value, *from_bits, *to_bits, *signed, *overflow)?;
        }

        MirInst::UnitSaturate { dest, value, min, max } => {
            compile_unit_saturate(ctx, builder, *dest, *value, *min, *max)?;
        }

        // Pointer instructions
        MirInst::PointerNew { dest, kind, value } => {
            compile_pointer_new(ctx, builder, *dest, *kind, *value)?;
        }

        MirInst::PointerRef { dest, kind, source } => {
            compile_pointer_ref(ctx, builder, *dest, *kind, *source)?;
        }

        MirInst::PointerDeref { dest, pointer, kind } => {
            compile_pointer_deref(ctx, builder, *dest, *pointer, *kind)?;
        }

        // GPU instructions
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

        MirInst::NeighborLoad { dest, array, direction } => {
            compile_neighbor_load(ctx, builder, *dest, *array, *direction)?;
        }

        // SIMD load/store operations
        MirInst::VecLoad { dest, array, offset } => {
            compile_vec_load(ctx, builder, *dest, *array, *offset)?;
        }

        MirInst::VecStore { source, array, offset } => {
            compile_vec_store(ctx, builder, *source, *array, *offset)?;
        }

        MirInst::VecGather { dest, array, indices } => {
            compile_vec_gather(ctx, builder, *dest, *array, *indices)?;
        }

        MirInst::VecScatter { source, array, indices } => {
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

        MirInst::VecClamp { dest, source, lo, hi } => {
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

        // Memory safety instructions
        MirInst::Drop { value, ty } => {
            // Drop is a no-op for primitive types
            // Primitive types: void, bool, integers (i8-i64, u8-u64), floats (f32, f64), string, nil
            let is_primitive = matches!(
                *ty,
                crate::hir::TypeId::VOID
                    | crate::hir::TypeId::BOOL
                    | crate::hir::TypeId::I8
                    | crate::hir::TypeId::I16
                    | crate::hir::TypeId::I32
                    | crate::hir::TypeId::I64
                    | crate::hir::TypeId::U8
                    | crate::hir::TypeId::U16
                    | crate::hir::TypeId::U32
                    | crate::hir::TypeId::U64
                    | crate::hir::TypeId::F32
                    | crate::hir::TypeId::F64
                    | crate::hir::TypeId::STRING
                    | crate::hir::TypeId::NIL
            );

            if !is_primitive {
                // Non-primitive types may need destructor calls
                // For now, we don't have a Drop trait in Simple, so this is a no-op
                // Future enhancement: look up Drop trait implementation in trait registry
                // and generate: call drop_fn(value)
                //
                // Implementation steps when Drop trait is added:
                // 1. Check if type implements Drop trait via ctx.module.trait_impls
                // 2. If yes, get the drop method function pointer
                // 3. Generate: builder.ins().call(drop_fn, &[value])
                //
                // For reference-counted types (Rc, Arc), the ref-count decrement
                // is handled by MirInst::RcDecrement / MirInst::WeakDecrement
                let _ = value; // Suppress unused warning
            }
        }

        MirInst::EndScope { local_index } => {
            // No-op at runtime - this is just a marker for lifetime analysis
            let _ = local_index; // Suppress unused warnings
        }

        // Value boxing instructions for FFI boundary
        MirInst::BoxInt { dest, value } => {
            // Box integer as RuntimeValue: (value << 3) | TAG_INT
            // TAG_INT is 0, so this is equivalent to value << 3
            let mut val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG BoxInt] Missing VReg {:?}, using default 0", value);
                builder.ins().iconst(types::I64, 0)
            });
            // Ensure value is i64 - some paths may produce i32 (e.g., FFI returns)
            let val_type = builder.func.dfg.value_type(val);
            if val_type == types::I32 {
                val = builder.ins().sextend(types::I64, val);
            } else if val_type == types::I8 || val_type == types::I16 {
                val = builder.ins().sextend(types::I64, val);
            }
            let three = builder.ins().iconst(types::I64, 3);
            let boxed = builder.ins().ishl(val, three);
            ctx.vreg_values.insert(*dest, boxed);
        }

        MirInst::BoxFloat { dest, value } => {
            // Box float as RuntimeValue: (bits >> 3) << 3 | TAG_FLOAT
            // TAG_FLOAT is 2 (0b010)
            let val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG BoxFloat] Missing VReg {:?}, using default 0", value);
                builder.ins().f64const(0.0)
            });
            let bits = builder.ins().bitcast(types::I64, MemFlags::new(), val);
            let three = builder.ins().iconst(types::I64, 3);
            let shifted = builder.ins().ushr(bits, three);
            let payload = builder.ins().ishl(shifted, three);
            let tag = builder.ins().iconst(types::I64, 2); // TAG_FLOAT
            let boxed = builder.ins().bor(payload, tag);
            ctx.vreg_values.insert(*dest, boxed);
        }

        MirInst::UnboxInt { dest, value } => {
            // Unbox RuntimeValue to integer: value >> 3 (arithmetic shift for sign extension)
            let val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG UnboxInt] Missing VReg {:?}, using default 0", value);
                builder.ins().iconst(types::I64, 0)
            });
            let three = builder.ins().iconst(types::I64, 3);
            let unboxed = builder.ins().sshr(val, three);
            ctx.vreg_values.insert(*dest, unboxed);
        }

        MirInst::UnboxFloat { dest, value } => {
            // Unbox RuntimeValue to float: extract bits and shift back
            let val = ctx.vreg_values.get(value).copied().unwrap_or_else(|| {
                eprintln!("[DEBUG UnboxFloat] Missing VReg {:?}, using default 0", value);
                builder.ins().iconst(types::I64, 0)
            });
            let three = builder.ins().iconst(types::I64, 3);
            let shifted = builder.ins().ushr(val, three);
            let bits = builder.ins().ishl(shifted, three);
            let unboxed = builder.ins().bitcast(types::F64, MemFlags::new(), bits);
            ctx.vreg_values.insert(*dest, unboxed);
        }
    }
    Ok(())
}
