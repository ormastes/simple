//! Generic instruction dispatch for any `CodegenEmitter` backend.
//!
//! This module provides `dispatch_instruction()` which maps each `MirInst` variant
//! to the corresponding `CodegenEmitter` method, eliminating per-backend dispatch duplication.

use crate::mir::MirInst;

use super::emitter_trait::CodegenEmitter;

/// Dispatch a single MIR instruction to the appropriate emitter method.
///
/// This is the single point of truth for MIR→backend lowering. Every backend
/// that implements `CodegenEmitter` gets instruction dispatch for free.
pub fn dispatch_instruction<E: CodegenEmitter>(emitter: &mut E, inst: &MirInst) -> Result<(), E::Error> {
    match inst {
        // =====================================================================
        // Constants
        // =====================================================================
        MirInst::ConstInt { dest, value } => emitter.emit_const_int(*dest, *value),
        MirInst::ConstFloat { dest, value } => emitter.emit_const_float(*dest, *value),
        MirInst::ConstBool { dest, value } => emitter.emit_const_bool(*dest, *value),
        MirInst::ConstString { dest, value } => emitter.emit_const_string(*dest, value),
        MirInst::ConstSymbol { dest, value } => emitter.emit_const_symbol(*dest, value),

        // =====================================================================
        // Basic operations
        // =====================================================================
        MirInst::Copy { dest, src } => emitter.emit_copy(*dest, *src),
        MirInst::BinOp { dest, op, left, right } => emitter.emit_binop(*dest, *op, *left, *right),
        MirInst::UnaryOp { dest, op, operand } => emitter.emit_unary_op(*dest, *op, *operand),
        MirInst::Cast {
            dest,
            source,
            from_ty,
            to_ty,
        } => emitter.emit_cast(*dest, *source, *from_ty, *to_ty),
        MirInst::Spread { dest, source } => emitter.emit_spread(*dest, *source),

        // =====================================================================
        // Memory
        // =====================================================================
        MirInst::Load { dest, addr, .. } => emitter.emit_load(*dest, *addr),
        MirInst::Store { addr, value, .. } => emitter.emit_store(*addr, *value),
        MirInst::GlobalLoad { dest, global_name, ty } => emitter.emit_global_load(*dest, global_name, *ty),
        MirInst::GlobalStore { global_name, value, ty } => emitter.emit_global_store(global_name, *value, *ty),
        MirInst::LocalAddr { dest, local_index } => emitter.emit_local_addr(*dest, *local_index),
        MirInst::GetElementPtr { dest, base, index } => emitter.emit_get_element_ptr(*dest, *base, *index),
        MirInst::GcAlloc { dest, ty } => emitter.emit_gc_alloc(*dest, *ty),
        MirInst::Wait { dest, target } => emitter.emit_wait(*dest, *target),

        // =====================================================================
        // Calls
        // =====================================================================
        MirInst::Call { dest, target, args } => emitter.emit_call(dest, target, args),
        MirInst::InterpCall { dest, func_name, args } => emitter.emit_interp_call(dest, func_name, args),
        MirInst::InterpEval { dest, expr_index } => emitter.emit_interp_eval(*dest, *expr_index as usize),
        MirInst::IndirectCall {
            dest,
            callee,
            param_types,
            return_type,
            args,
            effect,
        } => emitter.emit_indirect_call(dest, *callee, param_types, *return_type, args, *effect),

        // =====================================================================
        // Collections
        // =====================================================================
        MirInst::ArrayLit { dest, elements } => emitter.emit_array_lit(*dest, elements),
        MirInst::TupleLit { dest, elements } => emitter.emit_tuple_lit(*dest, elements),
        MirInst::VecLit { dest, elements } => emitter.emit_vec_lit(*dest, elements),
        MirInst::DictLit { dest, keys, values } => emitter.emit_dict_lit(*dest, keys, values),
        MirInst::IndexGet {
            dest,
            collection,
            index,
        } => emitter.emit_index_get(*dest, *collection, *index),
        MirInst::IndexSet {
            collection,
            index,
            value,
        } => emitter.emit_index_set(*collection, *index, *value),
        MirInst::SliceOp {
            dest,
            collection,
            start,
            end,
            step,
        } => emitter.emit_slice_op(*dest, *collection, *start, *end, *step),
        MirInst::FStringFormat { dest, parts } => emitter.emit_fstring_format(*dest, parts),

        // =====================================================================
        // SIMD vector operations
        // =====================================================================
        MirInst::VecSum { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_sum"),
        MirInst::VecProduct { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_product"),
        MirInst::VecMin { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_min"),
        MirInst::VecMax { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_max"),
        MirInst::VecAll { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_all"),
        MirInst::VecAny { dest, source } => emitter.emit_vec_reduction(*dest, *source, "rt_vec_any"),
        MirInst::VecExtract { dest, vector, index } => emitter.emit_vec_extract(*dest, *vector, *index),
        MirInst::VecWith {
            dest,
            vector,
            index,
            value,
        } => emitter.emit_vec_with(*dest, *vector, *index, *value),
        MirInst::VecSqrt { dest, source } => emitter.emit_vec_math(*dest, *source, "rt_vec_sqrt"),
        MirInst::VecAbs { dest, source } => emitter.emit_vec_math(*dest, *source, "rt_vec_abs"),
        MirInst::VecFloor { dest, source } => emitter.emit_vec_math(*dest, *source, "rt_vec_floor"),
        MirInst::VecCeil { dest, source } => emitter.emit_vec_math(*dest, *source, "rt_vec_ceil"),
        MirInst::VecRound { dest, source } => emitter.emit_vec_math(*dest, *source, "rt_vec_round"),
        MirInst::VecShuffle { dest, source, indices } => emitter.emit_vec_shuffle(*dest, *source, *indices),
        MirInst::VecBlend {
            dest,
            first,
            second,
            indices,
        } => emitter.emit_vec_blend(*dest, *first, *second, *indices),
        MirInst::VecSelect {
            dest,
            mask,
            if_true,
            if_false,
        } => emitter.emit_vec_select(*dest, *mask, *if_true, *if_false),
        MirInst::VecLoad { dest, array, offset } => emitter.emit_vec_load(*dest, *array, *offset),
        MirInst::VecStore { source, array, offset } => emitter.emit_vec_store(*source, *array, *offset),
        MirInst::VecGather { dest, array, indices } => emitter.emit_vec_gather(*dest, *array, *indices),
        MirInst::VecScatter { source, array, indices } => emitter.emit_vec_scatter(*source, *array, *indices),
        MirInst::VecFma { dest, a, b, c } => emitter.emit_vec_fma(*dest, *a, *b, *c),
        MirInst::VecRecip { dest, source } => emitter.emit_vec_recip(*dest, *source),
        MirInst::VecMaskedLoad {
            dest,
            array,
            offset,
            mask,
            default,
        } => emitter.emit_vec_masked_load(*dest, *array, *offset, *mask, *default),
        MirInst::VecMaskedStore {
            source,
            array,
            offset,
            mask,
        } => emitter.emit_vec_masked_store(*source, *array, *offset, *mask),
        MirInst::VecMinVec { dest, a, b } => emitter.emit_vec_min_vec(*dest, *a, *b),
        MirInst::VecMaxVec { dest, a, b } => emitter.emit_vec_max_vec(*dest, *a, *b),
        MirInst::VecClamp { dest, source, lo, hi } => emitter.emit_vec_clamp(*dest, *source, *lo, *hi),
        MirInst::NeighborLoad { dest, array, direction } => emitter.emit_neighbor_load(*dest, *array, *direction),

        // =====================================================================
        // Structs / Fields
        // =====================================================================
        MirInst::StructInit {
            dest,
            type_id: _,
            struct_size,
            field_offsets,
            field_types,
            field_values,
        } => emitter.emit_struct_init(*dest, *struct_size as usize, field_offsets, field_types, field_values),
        MirInst::FieldGet {
            dest,
            object,
            byte_offset,
            field_type,
        } => emitter.emit_field_get(*dest, *object, *byte_offset as usize, *field_type),
        MirInst::FieldSet {
            object,
            byte_offset,
            field_type,
            value,
        } => emitter.emit_field_set(*object, *byte_offset as usize, *field_type, *value),

        // =====================================================================
        // Closures
        // =====================================================================
        MirInst::ClosureCreate {
            dest,
            func_name,
            closure_size,
            capture_offsets,
            capture_types: _,
            captures,
        } => emitter.emit_closure_create(*dest, func_name, *closure_size as usize, capture_offsets, captures),

        // =====================================================================
        // Methods
        // =====================================================================
        MirInst::MethodCallStatic {
            dest,
            receiver,
            func_name,
            args,
        } => emitter.emit_method_call_static(dest, *receiver, func_name, args),
        MirInst::MethodCallVirtual {
            dest,
            receiver,
            vtable_slot,
            param_types,
            return_type,
            args,
        } => emitter.emit_method_call_virtual(dest, *receiver, *vtable_slot as usize, param_types, *return_type, args),
        MirInst::BuiltinMethod {
            dest,
            receiver,
            receiver_type,
            method,
            args,
        } => emitter.emit_builtin_method(dest, *receiver, receiver_type, method, args),
        MirInst::ExternMethodCall {
            dest,
            receiver,
            class_name,
            method_name,
            is_static,
            args,
        } => emitter.emit_extern_method_call(
            dest,
            receiver.as_ref().copied(),
            class_name,
            method_name,
            *is_static,
            args,
        ),

        // =====================================================================
        // Pattern matching
        // =====================================================================
        MirInst::PatternTest { dest, subject, pattern } => emitter.emit_pattern_test(*dest, *subject, pattern),
        MirInst::PatternBind { dest, subject, binding } => emitter.emit_pattern_bind(*dest, *subject, binding),

        // =====================================================================
        // Enums / Unions
        // =====================================================================
        MirInst::EnumDiscriminant { dest, value } => emitter.emit_enum_discriminant(*dest, *value),
        MirInst::EnumPayload { dest, value } => emitter.emit_enum_payload(*dest, *value),
        MirInst::EnumUnit {
            dest,
            enum_name: _,
            variant_name,
        } => emitter.emit_enum_unit(*dest, variant_name),
        MirInst::EnumWith {
            dest,
            enum_name: _,
            variant_name,
            payload,
        } => emitter.emit_enum_with(*dest, variant_name, *payload),
        MirInst::UnionDiscriminant { dest, value } => emitter.emit_union_discriminant(*dest, *value),
        MirInst::UnionPayload {
            dest,
            value,
            type_index: _,
        } => emitter.emit_union_payload(*dest, *value),
        MirInst::UnionWrap {
            dest,
            value,
            type_index,
        } => emitter.emit_union_wrap(*dest, *value, *type_index as u32),

        // =====================================================================
        // Async / Concurrency
        // =====================================================================
        MirInst::FutureCreate { dest, body_block } => emitter.emit_future_create(*dest, *body_block),
        MirInst::Await { dest, future } => emitter.emit_await(*dest, *future),
        MirInst::ActorSpawn { dest, body_block } => emitter.emit_actor_spawn(*dest, *body_block),
        MirInst::ActorSend { actor, message } => emitter.emit_actor_send(*actor, *message),
        MirInst::ActorRecv { dest } => emitter.emit_actor_recv(*dest),
        MirInst::ActorJoin { dest, actor } => emitter.emit_actor_join(*dest, *actor),
        MirInst::ActorReply { message } => emitter.emit_actor_reply(*message),
        MirInst::GeneratorCreate { dest, body_block } => emitter.emit_generator_create(*dest, *body_block),
        MirInst::Yield { value } => emitter.emit_yield(*value),
        MirInst::GeneratorNext { dest, generator } => emitter.emit_generator_next(*dest, *generator),

        // =====================================================================
        // Result / Option
        // =====================================================================
        MirInst::TryUnwrap {
            dest,
            value,
            error_block,
            error_dest,
        } => emitter.emit_try_unwrap(*dest, *value, *error_block, *error_dest),
        MirInst::OptionSome { dest, value } => emitter.emit_option_some(*dest, *value),
        MirInst::OptionNone { dest } => emitter.emit_option_none(*dest),
        MirInst::ResultOk { dest, value } => emitter.emit_result_ok(*dest, *value),
        MirInst::ResultErr { dest, value } => emitter.emit_result_err(*dest, *value),

        // =====================================================================
        // Contracts
        // =====================================================================
        MirInst::ContractCheck {
            condition,
            kind,
            func_name,
            message,
        } => emitter.emit_contract_check(*condition, *kind, func_name, message.as_deref()),
        MirInst::ContractOldCapture { dest, value } => emitter.emit_contract_old_capture(*dest, *value),

        // =====================================================================
        // Coverage
        // =====================================================================
        MirInst::DecisionProbe {
            result,
            decision_id,
            file,
            line,
            column,
        } => emitter.emit_decision_probe(*result, *decision_id, file, *line, *column),
        MirInst::ConditionProbe {
            decision_id,
            condition_id,
            result,
            file,
            line,
            column,
        } => emitter.emit_condition_probe(*decision_id, *condition_id, *result, file, *line, *column),
        MirInst::PathProbe { path_id, block_id } => emitter.emit_path_probe(*path_id, *block_id),

        // =====================================================================
        // Units
        // =====================================================================
        MirInst::UnitBoundCheck {
            value,
            unit_name,
            min,
            max,
            overflow,
        } => emitter.emit_unit_bound_check(*value, unit_name, *min, *max, *overflow),
        MirInst::UnitWiden {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
        } => emitter.emit_unit_widen(*dest, *value, *from_bits, *to_bits, *signed),
        MirInst::UnitNarrow {
            dest,
            value,
            from_bits,
            to_bits,
            signed,
            overflow,
        } => emitter.emit_unit_narrow(*dest, *value, *from_bits, *to_bits, *signed, *overflow),
        MirInst::UnitSaturate { dest, value, min, max } => emitter.emit_unit_saturate(*dest, *value, *min, *max),

        // =====================================================================
        // Pointers
        // =====================================================================
        MirInst::PointerNew { dest, kind, value } => emitter.emit_pointer_new(*dest, *kind, *value),
        MirInst::PointerRef { dest, kind, source } => emitter.emit_pointer_ref(*dest, *kind, *source),
        MirInst::PointerDeref { dest, pointer, kind } => emitter.emit_pointer_deref(*dest, *pointer, *kind),

        // =====================================================================
        // Memory safety (no-ops)
        // =====================================================================
        MirInst::Drop { value, ty } => emitter.emit_drop(*value, *ty),
        MirInst::EndScope { local_index } => emitter.emit_end_scope(*local_index),

        // =====================================================================
        // Boxing
        // =====================================================================
        MirInst::BoxInt { dest, value } => emitter.emit_box_int(*dest, *value),
        MirInst::BoxFloat { dest, value } => emitter.emit_box_float(*dest, *value),
        MirInst::UnboxInt { dest, value } => emitter.emit_unbox_int(*dest, *value),
        MirInst::UnboxFloat { dest, value } => emitter.emit_unbox_float(*dest, *value),

        // =====================================================================
        // GPU
        // =====================================================================
        MirInst::GpuGlobalId { dest, dim } => emitter.emit_gpu_global_id(*dest, *dim),
        MirInst::GpuLocalId { dest, dim } => emitter.emit_gpu_local_id(*dest, *dim),
        MirInst::GpuGroupId { dest, dim } => emitter.emit_gpu_group_id(*dest, *dim),
        MirInst::GpuGlobalSize { dest, dim } => emitter.emit_gpu_global_size(*dest, *dim),
        MirInst::GpuLocalSize { dest, dim } => emitter.emit_gpu_local_size(*dest, *dim),
        MirInst::GpuNumGroups { dest, dim } => emitter.emit_gpu_num_groups(*dest, *dim),
        MirInst::GpuBarrier => emitter.emit_gpu_barrier(),
        MirInst::GpuMemFence { scope } => emitter.emit_gpu_mem_fence(*scope),
        MirInst::GpuSharedAlloc {
            dest,
            element_type,
            size,
        } => emitter.emit_gpu_shared_alloc(*dest, *element_type, *size),
        MirInst::GpuAtomic { dest, op, ptr, value } => emitter.emit_gpu_atomic(*dest, *op, *ptr, *value),
        MirInst::GpuAtomicCmpXchg {
            dest,
            ptr,
            expected,
            desired,
        } => emitter.emit_gpu_atomic_cmpxchg(*dest, *ptr, *expected, *desired),

        // =====================================================================
        // Parallel iterators
        // =====================================================================
        MirInst::ParMap {
            dest,
            input,
            closure,
            backend,
        } => emitter.emit_par_map(*dest, *input, *closure, *backend),
        MirInst::ParReduce {
            dest,
            input,
            initial,
            closure,
            backend,
        } => emitter.emit_par_reduce(*dest, *input, *initial, *closure, *backend),
        MirInst::ParFilter {
            dest,
            input,
            predicate,
            backend,
        } => emitter.emit_par_filter(*dest, *input, *predicate, *backend),
        MirInst::ParForEach {
            input,
            closure,
            backend,
        } => emitter.emit_par_for_each(*input, *closure, *backend),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::VReg;

    /// Verify that dispatch_instruction handles every MirInst variant.
    /// This test is compile-time exhaustiveness — if a new variant is added
    /// to MirInst, this file will fail to compile until the match is updated.
    #[test]
    fn dispatch_is_exhaustive() {
        // The fact that dispatch_instruction compiles with no wildcard
        // match arm proves it handles every MirInst variant.
        // This test simply asserts the function exists and compiles.
        fn _assert_compiles<E: CodegenEmitter>(_e: &mut E, _i: &MirInst) -> Result<(), E::Error> {
            dispatch_instruction(_e, _i)
        }
    }
}
