//! Unified codegen emitter trait for all MIR-based backends.
//!
//! Each backend (Cranelift, LLVM, Vulkan) implements `CodegenEmitter`,
//! enabling a single generic `dispatch_instruction()` to drive any backend.

use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};
use crate::mir::{
    BlockId, CallTarget, ContractKind, Effect, FStringPart, GpuAtomicOp, GpuMemoryScope, MirPattern, ParallelBackend,
    PatternBinding, UnitOverflowBehavior, VReg,
};

/// Unified instruction emission interface for MIR-based backends.
///
/// Each associated type represents the backend's native value handle:
/// - Cranelift: `cranelift_codegen::ir::Value`
/// - LLVM: `inkwell::values::BasicValueEnum`
/// - Vulkan: SPIR-V result ID
pub trait CodegenEmitter {
    /// The value handle type for this backend (SSA value, SPIR-V ID, etc.)
    type Value: Copy;
    /// The error type for this backend
    type Error: From<String>;

    // =========================================================================
    // Constants
    // =========================================================================
    fn emit_const_int(&mut self, dest: VReg, value: i64) -> Result<(), Self::Error>;
    fn emit_const_float(&mut self, dest: VReg, value: f64) -> Result<(), Self::Error>;
    fn emit_const_bool(&mut self, dest: VReg, value: bool) -> Result<(), Self::Error>;
    fn emit_const_string(&mut self, dest: VReg, value: &str) -> Result<(), Self::Error>;
    fn emit_const_symbol(&mut self, dest: VReg, value: &str) -> Result<(), Self::Error>;

    // =========================================================================
    // Basic operations
    // =========================================================================
    fn emit_copy(&mut self, dest: VReg, src: VReg) -> Result<(), Self::Error>;
    fn emit_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg) -> Result<(), Self::Error>;
    fn emit_unary_op(&mut self, dest: VReg, op: UnaryOp, operand: VReg) -> Result<(), Self::Error>;
    fn emit_cast(&mut self, dest: VReg, source: VReg, from_ty: TypeId, to_ty: TypeId) -> Result<(), Self::Error>;
    fn emit_spread(&mut self, dest: VReg, source: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // Memory
    // =========================================================================
    fn emit_load(&mut self, dest: VReg, addr: VReg) -> Result<(), Self::Error>;
    fn emit_store(&mut self, addr: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_global_load(&mut self, dest: VReg, global_name: &str, ty: TypeId) -> Result<(), Self::Error>;
    fn emit_global_store(&mut self, global_name: &str, value: VReg, ty: TypeId) -> Result<(), Self::Error>;
    fn emit_local_addr(&mut self, dest: VReg, local_index: usize) -> Result<(), Self::Error>;
    fn emit_get_element_ptr(&mut self, dest: VReg, base: VReg, index: VReg) -> Result<(), Self::Error>;
    fn emit_gc_alloc(&mut self, dest: VReg, ty: TypeId) -> Result<(), Self::Error>;
    fn emit_wait(&mut self, dest: Option<VReg>, target: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // Calls
    // =========================================================================
    fn emit_call(&mut self, dest: &Option<VReg>, target: &CallTarget, args: &[VReg]) -> Result<(), Self::Error>;
    fn emit_interp_call(&mut self, dest: &Option<VReg>, func_name: &str, args: &[VReg]) -> Result<(), Self::Error>;
    fn emit_interp_eval(&mut self, dest: VReg, expr_index: usize) -> Result<(), Self::Error>;
    fn emit_indirect_call(
        &mut self,
        dest: &Option<VReg>,
        callee: VReg,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
        effect: Effect,
    ) -> Result<(), Self::Error>;

    // =========================================================================
    // Collections
    // =========================================================================
    fn emit_array_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), Self::Error>;
    fn emit_tuple_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), Self::Error>;
    fn emit_vec_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), Self::Error>;
    fn emit_dict_lit(&mut self, dest: VReg, keys: &[VReg], values: &[VReg]) -> Result<(), Self::Error>;
    fn emit_index_get(&mut self, dest: VReg, collection: VReg, index: VReg) -> Result<(), Self::Error>;
    fn emit_index_set(&mut self, collection: VReg, index: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_slice_op(
        &mut self,
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    ) -> Result<(), Self::Error>;
    fn emit_fstring_format(&mut self, dest: VReg, parts: &[FStringPart]) -> Result<(), Self::Error>;

    // =========================================================================
    // SIMD / Vector operations
    // =========================================================================
    fn emit_vec_reduction(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), Self::Error>;
    fn emit_vec_extract(&mut self, dest: VReg, vector: VReg, index: VReg) -> Result<(), Self::Error>;
    fn emit_vec_with(&mut self, dest: VReg, vector: VReg, index: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_vec_math(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), Self::Error>;
    fn emit_vec_shuffle(&mut self, dest: VReg, source: VReg, indices: VReg) -> Result<(), Self::Error>;
    fn emit_vec_blend(&mut self, dest: VReg, first: VReg, second: VReg, indices: VReg) -> Result<(), Self::Error>;
    fn emit_vec_select(&mut self, dest: VReg, mask: VReg, if_true: VReg, if_false: VReg) -> Result<(), Self::Error>;
    fn emit_vec_load(&mut self, dest: VReg, array: VReg, offset: VReg) -> Result<(), Self::Error>;
    fn emit_vec_store(&mut self, source: VReg, array: VReg, offset: VReg) -> Result<(), Self::Error>;
    fn emit_vec_gather(&mut self, dest: VReg, array: VReg, indices: VReg) -> Result<(), Self::Error>;
    fn emit_vec_scatter(&mut self, source: VReg, array: VReg, indices: VReg) -> Result<(), Self::Error>;
    fn emit_vec_fma(&mut self, dest: VReg, a: VReg, b: VReg, c: VReg) -> Result<(), Self::Error>;
    fn emit_vec_recip(&mut self, dest: VReg, source: VReg) -> Result<(), Self::Error>;
    fn emit_vec_masked_load(
        &mut self,
        dest: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
        default: VReg,
    ) -> Result<(), Self::Error>;
    fn emit_vec_masked_store(&mut self, source: VReg, array: VReg, offset: VReg, mask: VReg)
        -> Result<(), Self::Error>;
    fn emit_vec_min_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), Self::Error>;
    fn emit_vec_max_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), Self::Error>;
    fn emit_vec_clamp(&mut self, dest: VReg, source: VReg, lo: VReg, hi: VReg) -> Result<(), Self::Error>;
    fn emit_neighbor_load(&mut self, dest: VReg, array: VReg, direction: NeighborDirection) -> Result<(), Self::Error>;

    // =========================================================================
    // Structs / Fields
    // =========================================================================
    fn emit_struct_init(
        &mut self,
        dest: VReg,
        struct_size: usize,
        field_offsets: &[u32],
        field_types: &[TypeId],
        field_values: &[VReg],
    ) -> Result<(), Self::Error>;
    fn emit_field_get(
        &mut self,
        dest: VReg,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
    ) -> Result<(), Self::Error>;
    fn emit_field_set(
        &mut self,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
        value: VReg,
    ) -> Result<(), Self::Error>;

    // =========================================================================
    // Closures
    // =========================================================================
    fn emit_closure_create(
        &mut self,
        dest: VReg,
        func_name: &str,
        closure_size: usize,
        capture_offsets: &[u32],
        captures: &[VReg],
    ) -> Result<(), Self::Error>;

    // =========================================================================
    // Methods
    // =========================================================================
    fn emit_method_call_static(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        func_name: &str,
        args: &[VReg],
    ) -> Result<(), Self::Error>;
    fn emit_method_call_virtual(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        vtable_slot: usize,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
    ) -> Result<(), Self::Error>;
    fn emit_builtin_method(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        receiver_type: &str,
        method: &str,
        args: &[VReg],
    ) -> Result<(), Self::Error>;
    fn emit_extern_method_call(
        &mut self,
        dest: &Option<VReg>,
        receiver: Option<VReg>,
        class_name: &str,
        method_name: &str,
        is_static: bool,
        args: &[VReg],
    ) -> Result<(), Self::Error>;

    // =========================================================================
    // Pattern matching
    // =========================================================================
    fn emit_pattern_test(&mut self, dest: VReg, subject: VReg, pattern: &MirPattern) -> Result<(), Self::Error>;
    fn emit_pattern_bind(&mut self, dest: VReg, subject: VReg, binding: &PatternBinding) -> Result<(), Self::Error>;

    // =========================================================================
    // Enums / Unions
    // =========================================================================
    fn emit_enum_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_enum_payload(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_enum_unit(&mut self, dest: VReg, variant_name: &str) -> Result<(), Self::Error>;
    fn emit_enum_with(&mut self, dest: VReg, variant_name: &str, payload: VReg) -> Result<(), Self::Error>;
    fn emit_union_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_union_payload(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_union_wrap(&mut self, dest: VReg, value: VReg, type_index: u32) -> Result<(), Self::Error>;

    // =========================================================================
    // Async / Concurrency
    // =========================================================================
    fn emit_future_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), Self::Error>;
    fn emit_await(&mut self, dest: VReg, future: VReg) -> Result<(), Self::Error>;
    fn emit_actor_spawn(&mut self, dest: VReg, body_block: BlockId) -> Result<(), Self::Error>;
    fn emit_actor_send(&mut self, actor: VReg, message: VReg) -> Result<(), Self::Error>;
    fn emit_actor_recv(&mut self, dest: VReg) -> Result<(), Self::Error>;
    fn emit_actor_join(&mut self, dest: VReg, actor: VReg) -> Result<(), Self::Error>;
    fn emit_actor_reply(&mut self, message: VReg) -> Result<(), Self::Error>;
    fn emit_generator_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), Self::Error>;
    fn emit_yield(&mut self, value: VReg) -> Result<(), Self::Error>;
    fn emit_generator_next(&mut self, dest: VReg, generator: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // Result / Option
    // =========================================================================
    fn emit_try_unwrap(
        &mut self,
        dest: VReg,
        value: VReg,
        error_block: BlockId,
        error_dest: VReg,
    ) -> Result<(), Self::Error>;
    fn emit_option_some(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_option_none(&mut self, dest: VReg) -> Result<(), Self::Error>;
    fn emit_result_ok(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_result_err(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // Contracts
    // =========================================================================
    fn emit_contract_check(
        &mut self,
        condition: VReg,
        kind: ContractKind,
        func_name: &str,
        message: Option<&str>,
    ) -> Result<(), Self::Error>;
    fn emit_contract_old_capture(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // Coverage
    // =========================================================================
    fn emit_decision_probe(
        &mut self,
        result: VReg,
        decision_id: u32,
        file: &str,
        line: u32,
        column: u32,
    ) -> Result<(), Self::Error>;
    fn emit_condition_probe(
        &mut self,
        decision_id: u32,
        condition_id: u32,
        result: VReg,
        file: &str,
        line: u32,
        column: u32,
    ) -> Result<(), Self::Error>;
    fn emit_path_probe(&mut self, path_id: u32, block_id: u32) -> Result<(), Self::Error>;

    // =========================================================================
    // Units
    // =========================================================================
    fn emit_unit_bound_check(
        &mut self,
        value: VReg,
        unit_name: &str,
        min: i64,
        max: i64,
        overflow: UnitOverflowBehavior,
    ) -> Result<(), Self::Error>;
    fn emit_unit_widen(
        &mut self,
        dest: VReg,
        value: VReg,
        from_bits: u8,
        to_bits: u8,
        signed: bool,
    ) -> Result<(), Self::Error>;
    fn emit_unit_narrow(
        &mut self,
        dest: VReg,
        value: VReg,
        from_bits: u8,
        to_bits: u8,
        signed: bool,
        overflow: UnitOverflowBehavior,
    ) -> Result<(), Self::Error>;
    fn emit_unit_saturate(&mut self, dest: VReg, value: VReg, min: i64, max: i64) -> Result<(), Self::Error>;

    // =========================================================================
    // Pointers
    // =========================================================================
    fn emit_pointer_new(&mut self, dest: VReg, kind: PointerKind, value: VReg) -> Result<(), Self::Error>;
    fn emit_pointer_ref(&mut self, dest: VReg, kind: PointerKind, source: VReg) -> Result<(), Self::Error>;
    fn emit_pointer_deref(&mut self, dest: VReg, pointer: VReg, kind: PointerKind) -> Result<(), Self::Error>;

    // =========================================================================
    // Memory safety (no-ops for most backends)
    // =========================================================================
    fn emit_drop(&mut self, _value: VReg, _ty: TypeId) -> Result<(), Self::Error> {
        Ok(()) // Default: no-op
    }
    fn emit_end_scope(&mut self, _local_index: usize) -> Result<(), Self::Error> {
        Ok(()) // Default: no-op
    }

    // =========================================================================
    // Boxing (FFI boundary)
    // =========================================================================
    fn emit_box_int(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_box_float(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_unbox_int(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_unbox_float(&mut self, dest: VReg, value: VReg) -> Result<(), Self::Error>;

    // =========================================================================
    // GPU instructions
    // =========================================================================
    fn emit_gpu_global_id(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_local_id(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_group_id(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_global_size(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_local_size(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_num_groups(&mut self, dest: VReg, dim: u8) -> Result<(), Self::Error>;
    fn emit_gpu_barrier(&mut self) -> Result<(), Self::Error>;
    fn emit_gpu_mem_fence(&mut self, scope: GpuMemoryScope) -> Result<(), Self::Error>;
    fn emit_gpu_shared_alloc(&mut self, dest: VReg, element_type: TypeId, size: u32) -> Result<(), Self::Error>;
    fn emit_gpu_atomic(&mut self, dest: VReg, op: GpuAtomicOp, ptr: VReg, value: VReg) -> Result<(), Self::Error>;
    fn emit_gpu_atomic_cmpxchg(
        &mut self,
        dest: VReg,
        ptr: VReg,
        expected: VReg,
        desired: VReg,
    ) -> Result<(), Self::Error>;

    // =========================================================================
    // Parallel iterators
    // =========================================================================
    fn emit_par_map(
        &mut self,
        dest: VReg,
        input: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error>;
    fn emit_par_reduce(
        &mut self,
        dest: VReg,
        input: VReg,
        initial: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error>;
    fn emit_par_filter(
        &mut self,
        dest: VReg,
        input: VReg,
        predicate: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error>;
    fn emit_par_for_each(
        &mut self,
        input: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), Self::Error>;
}
