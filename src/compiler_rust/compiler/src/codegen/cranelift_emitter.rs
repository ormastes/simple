//! Cranelift implementation of the `CodegenEmitter` trait.
//!
//! This is an adapter that wraps the existing `InstrContext<M>` + `FunctionBuilder`
//! and delegates to the existing `compile_*` functions in `instr/` submodules.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::{BinOp, NeighborDirection, PointerKind, TypeId, UnaryOp};
use crate::mir::{
    BlockId, CallTarget, ContractKind, Effect, FStringPart, GpuAtomicOp, GpuMemoryScope, MirPattern, ParallelBackend,
    PatternBinding, UnitOverflowBehavior, VReg,
};

use super::emitter_trait::CodegenEmitter;
use super::instr::InstrContext;

/// Cranelift-based emitter wrapping existing instruction compilation infrastructure.
///
/// This struct holds mutable references to the Cranelift compilation context
/// and function builder, delegating each trait method to the corresponding
/// `compile_*` function in `instr/` submodules.
pub struct CraneliftEmitter<'a, 'b, M: Module> {
    pub ctx: &'a mut InstrContext<'b, M>,
    pub builder: &'a mut FunctionBuilder<'b>,
}

impl<M: Module> CodegenEmitter for CraneliftEmitter<'_, '_, M> {
    type Value = cranelift_codegen::ir::Value;
    type Error = String;

    // =========================================================================
    // Constants
    // =========================================================================
    fn emit_const_int(&mut self, dest: VReg, value: i64) -> Result<(), String> {
        super::instr::constants::compile_const_int(self.ctx, self.builder, dest, value)
    }
    fn emit_const_float(&mut self, dest: VReg, value: f64) -> Result<(), String> {
        super::instr::constants::compile_const_float(self.ctx, self.builder, dest, value)
    }
    fn emit_const_bool(&mut self, dest: VReg, value: bool) -> Result<(), String> {
        super::instr::constants::compile_const_bool(self.ctx, self.builder, dest, value)
    }
    fn emit_const_string(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        super::instr::collections::compile_const_string(self.ctx, self.builder, dest, value);
        Ok(())
    }
    fn emit_const_symbol(&mut self, dest: VReg, value: &str) -> Result<(), String> {
        super::instr::constants::compile_const_symbol(self.ctx, self.builder, dest, value)
    }

    // =========================================================================
    // Basic operations
    // =========================================================================
    fn emit_copy(&mut self, dest: VReg, src: VReg) -> Result<(), String> {
        super::instr::basic_ops::compile_copy(self.ctx, self.builder, dest, src)
    }
    fn emit_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg) -> Result<(), String> {
        let lhs = self
            .ctx
            .vreg_values
            .get(&left)
            .copied()
            .unwrap_or_else(|| self.builder.ins().iconst(types::I64, 0));
        let rhs = self
            .ctx
            .vreg_values
            .get(&right)
            .copied()
            .unwrap_or_else(|| self.builder.ins().iconst(types::I64, 0));
        let val = super::instr::core::compile_binop(self.ctx, self.builder, op, lhs, rhs)?;
        self.ctx.vreg_values.insert(dest, val);
        Ok(())
    }
    fn emit_unary_op(&mut self, dest: VReg, op: UnaryOp, operand: VReg) -> Result<(), String> {
        super::instr::basic_ops::compile_unary_op(self.ctx, self.builder, dest, op, operand)
    }
    fn emit_cast(&mut self, dest: VReg, source: VReg, from_ty: TypeId, to_ty: TypeId) -> Result<(), String> {
        super::instr::basic_ops::compile_cast(self.ctx, self.builder, dest, source, from_ty, to_ty)
    }
    fn emit_spread(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        super::instr::basic_ops::compile_spread(self.ctx, self.builder, dest, source)
    }

    // =========================================================================
    // Memory
    // =========================================================================
    fn emit_load(&mut self, dest: VReg, addr: VReg) -> Result<(), String> {
        super::instr::memory::compile_load(self.ctx, self.builder, dest, addr)
    }
    fn emit_store(&mut self, addr: VReg, value: VReg) -> Result<(), String> {
        super::instr::memory::compile_store(self.ctx, self.builder, addr, value)
    }
    fn emit_global_load(&mut self, dest: VReg, global_name: &str, ty: TypeId) -> Result<(), String> {
        // First try regular global variables
        if let Some(&global_id) = self.ctx.global_ids.get(global_name) {
            let global_ref = self.ctx.module.declare_data_in_func(global_id, self.builder.func);
            let global_addr = self.builder.ins().global_value(types::I64, global_ref);
            let val = self.builder.ins().load(
                super::types_util::type_id_to_cranelift(ty),
                MemFlags::new(),
                global_addr,
                0,
            );
            self.ctx.vreg_values.insert(dest, val);
            return Ok(());
        }

        // Fallback: static method reference (e.g. "Point.origin") — resolve as function address
        if let Some(&func_id) = self.ctx.func_ids.get(global_name) {
            let func_ref = self.ctx.module.declare_func_in_func(func_id, self.builder.func);
            let addr = self.builder.ins().func_addr(types::I64, func_ref);
            self.ctx.vreg_values.insert(dest, addr);
            return Ok(());
        }

        Err(format!("Global variable '{}' not found", global_name))
    }
    fn emit_global_store(&mut self, global_name: &str, value: VReg, _ty: TypeId) -> Result<(), String> {
        let global_id = self
            .ctx
            .global_ids
            .get(global_name)
            .ok_or_else(|| format!("Global variable '{}' not found", global_name))?;
        let global_ref = self.ctx.module.declare_data_in_func(*global_id, self.builder.func);
        let global_addr = self.builder.ins().global_value(types::I64, global_ref);
        let val = self
            .ctx
            .vreg_values
            .get(&value)
            .ok_or_else(|| format!("GlobalStore: vreg {:?} not found", value))?;
        self.builder.ins().store(MemFlags::new(), *val, global_addr, 0);
        Ok(())
    }
    fn emit_local_addr(&mut self, dest: VReg, local_index: usize) -> Result<(), String> {
        super::instr::memory::compile_local_addr(self.ctx, self.builder, dest, local_index)
    }
    fn emit_get_element_ptr(&mut self, dest: VReg, base: VReg, index: VReg) -> Result<(), String> {
        super::instr::memory::compile_get_element_ptr(self.ctx, self.builder, dest, base, index)
    }
    fn emit_gc_alloc(&mut self, dest: VReg, ty: TypeId) -> Result<(), String> {
        super::instr::memory::compile_gc_alloc(self.ctx, self.builder, dest, ty)
    }
    fn emit_wait(&mut self, dest: Option<VReg>, target: VReg) -> Result<(), String> {
        super::instr::memory::compile_wait(self.ctx, self.builder, dest, target)
    }

    // =========================================================================
    // Calls
    // =========================================================================
    fn emit_call(&mut self, dest: &Option<VReg>, target: &CallTarget, args: &[VReg]) -> Result<(), String> {
        super::instr::calls::compile_call(self.ctx, self.builder, dest, target, args)
    }
    fn emit_interp_call(&mut self, dest: &Option<VReg>, func_name: &str, args: &[VReg]) -> Result<(), String> {
        super::instr::core::compile_interp_call(self.ctx, self.builder, dest, func_name, args)
    }
    fn emit_interp_eval(&mut self, dest: VReg, expr_index: usize) -> Result<(), String> {
        super::instr::interpreter::compile_interp_eval(self.ctx, self.builder, dest, expr_index)
    }
    fn emit_indirect_call(
        &mut self,
        dest: &Option<VReg>,
        callee: VReg,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
        _effect: Effect,
    ) -> Result<(), String> {
        super::instr::closures_structs::compile_indirect_call(
            self.ctx,
            self.builder,
            dest,
            callee,
            param_types,
            return_type,
            args,
        );
        Ok(())
    }

    // =========================================================================
    // Collections
    // =========================================================================
    fn emit_array_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        super::instr::collections::compile_array_lit(self.ctx, self.builder, dest, elements);
        Ok(())
    }
    fn emit_tuple_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        super::instr::collections::compile_tuple_lit(self.ctx, self.builder, dest, elements);
        Ok(())
    }
    fn emit_vec_lit(&mut self, dest: VReg, elements: &[VReg]) -> Result<(), String> {
        super::instr::collections::compile_vec_lit(self.ctx, self.builder, dest, elements);
        Ok(())
    }
    fn emit_dict_lit(&mut self, dest: VReg, keys: &[VReg], values: &[VReg]) -> Result<(), String> {
        super::instr::collections::compile_dict_lit(self.ctx, self.builder, dest, keys, values);
        Ok(())
    }
    fn emit_index_get(&mut self, dest: VReg, collection: VReg, index: VReg) -> Result<(), String> {
        super::instr::collections::compile_index_get(self.ctx, self.builder, dest, collection, index);
        Ok(())
    }
    fn emit_index_set(&mut self, collection: VReg, index: VReg, value: VReg) -> Result<(), String> {
        super::instr::collections::compile_index_set(self.ctx, self.builder, collection, index, value);
        Ok(())
    }
    fn emit_slice_op(
        &mut self,
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    ) -> Result<(), String> {
        super::instr::collections::compile_slice_op(self.ctx, self.builder, dest, collection, start, end, step);
        Ok(())
    }
    fn emit_fstring_format(&mut self, dest: VReg, parts: &[FStringPart]) -> Result<(), String> {
        super::instr::collections::compile_fstring_format(self.ctx, self.builder, dest, parts);
        Ok(())
    }

    // =========================================================================
    // SIMD / Vector
    // =========================================================================
    fn emit_vec_reduction(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        super::instr::collections::compile_vec_reduction(self.ctx, self.builder, dest, source, op);
        Ok(())
    }
    fn emit_vec_extract(&mut self, dest: VReg, vector: VReg, index: VReg) -> Result<(), String> {
        super::instr::collections::compile_vec_extract(self.ctx, self.builder, dest, vector, index);
        Ok(())
    }
    fn emit_vec_with(&mut self, dest: VReg, vector: VReg, index: VReg, value: VReg) -> Result<(), String> {
        super::instr::collections::compile_vec_with(self.ctx, self.builder, dest, vector, index, value);
        Ok(())
    }
    fn emit_vec_math(&mut self, dest: VReg, source: VReg, op: &str) -> Result<(), String> {
        super::instr::collections::compile_vec_math(self.ctx, self.builder, dest, source, op);
        Ok(())
    }
    fn emit_vec_shuffle(&mut self, dest: VReg, source: VReg, indices: VReg) -> Result<(), String> {
        super::instr::collections::compile_vec_shuffle(self.ctx, self.builder, dest, source, indices);
        Ok(())
    }
    fn emit_vec_blend(&mut self, dest: VReg, first: VReg, second: VReg, indices: VReg) -> Result<(), String> {
        super::instr::collections::compile_vec_blend(self.ctx, self.builder, dest, first, second, indices);
        Ok(())
    }
    fn emit_vec_select(&mut self, dest: VReg, mask: VReg, if_true: VReg, if_false: VReg) -> Result<(), String> {
        super::instr::collections::compile_vec_select(self.ctx, self.builder, dest, mask, if_true, if_false);
        Ok(())
    }
    fn emit_vec_load(&mut self, dest: VReg, array: VReg, offset: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_load(self.ctx, self.builder, dest, array, offset)
    }
    fn emit_vec_store(&mut self, source: VReg, array: VReg, offset: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_store(self.ctx, self.builder, source, array, offset)
    }
    fn emit_vec_gather(&mut self, dest: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_gather(self.ctx, self.builder, dest, array, indices)
    }
    fn emit_vec_scatter(&mut self, source: VReg, array: VReg, indices: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_scatter(self.ctx, self.builder, source, array, indices)
    }
    fn emit_vec_fma(&mut self, dest: VReg, a: VReg, b: VReg, c: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_fma(self.ctx, self.builder, dest, a, b, c)
    }
    fn emit_vec_recip(&mut self, dest: VReg, source: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_recip(self.ctx, self.builder, dest, source)
    }
    fn emit_vec_masked_load(
        &mut self,
        dest: VReg,
        array: VReg,
        offset: VReg,
        mask: VReg,
        default: VReg,
    ) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_masked_load(self.ctx, self.builder, dest, array, offset, mask, default)
    }
    fn emit_vec_masked_store(&mut self, source: VReg, array: VReg, offset: VReg, mask: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_masked_store(self.ctx, self.builder, source, array, offset, mask)
    }
    fn emit_vec_min_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_min_vec(self.ctx, self.builder, dest, a, b)
    }
    fn emit_vec_max_vec(&mut self, dest: VReg, a: VReg, b: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_max_vec(self.ctx, self.builder, dest, a, b)
    }
    fn emit_vec_clamp(&mut self, dest: VReg, source: VReg, lo: VReg, hi: VReg) -> Result<(), String> {
        super::instr::simd_stubs::compile_vec_clamp(self.ctx, self.builder, dest, source, lo, hi)
    }
    fn emit_neighbor_load(&mut self, dest: VReg, array: VReg, direction: NeighborDirection) -> Result<(), String> {
        super::instr::simd_stubs::compile_neighbor_load(self.ctx, self.builder, dest, array, direction)
    }

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
    ) -> Result<(), String> {
        super::instr::closures_structs::compile_struct_init(
            self.ctx,
            self.builder,
            dest,
            struct_size,
            field_offsets,
            field_types,
            field_values,
        );
        Ok(())
    }
    fn emit_field_get(
        &mut self,
        dest: VReg,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
    ) -> Result<(), String> {
        super::instr::fields::compile_field_get(self.ctx, self.builder, dest, object, byte_offset, field_type)
    }
    fn emit_field_set(
        &mut self,
        object: VReg,
        byte_offset: usize,
        field_type: TypeId,
        value: VReg,
    ) -> Result<(), String> {
        super::instr::fields::compile_field_set(self.ctx, self.builder, object, byte_offset, field_type, value)
    }

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
    ) -> Result<(), String> {
        super::instr::closures_structs::compile_closure_create(
            self.ctx,
            self.builder,
            dest,
            func_name,
            closure_size,
            capture_offsets,
            captures,
        );
        Ok(())
    }

    // =========================================================================
    // Methods
    // =========================================================================
    fn emit_method_call_static(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        func_name: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        super::instr::closures_structs::compile_method_call_static(
            self.ctx,
            self.builder,
            dest,
            receiver,
            func_name,
            args,
        )
    }
    fn emit_method_call_virtual(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        vtable_slot: usize,
        param_types: &[TypeId],
        return_type: TypeId,
        args: &[VReg],
    ) -> Result<(), String> {
        super::instr::closures_structs::compile_method_call_virtual(
            self.ctx,
            self.builder,
            dest,
            receiver,
            vtable_slot,
            param_types,
            return_type,
            args,
        );
        Ok(())
    }
    fn emit_builtin_method(
        &mut self,
        dest: &Option<VReg>,
        receiver: VReg,
        receiver_type: &str,
        method: &str,
        args: &[VReg],
    ) -> Result<(), String> {
        super::instr::methods::compile_builtin_method(
            self.ctx,
            self.builder,
            dest,
            receiver,
            receiver_type,
            method,
            args,
        )
    }
    fn emit_extern_method_call(
        &mut self,
        dest: &Option<VReg>,
        receiver: Option<VReg>,
        class_name: &str,
        method_name: &str,
        is_static: bool,
        args: &[VReg],
    ) -> Result<(), String> {
        super::instr::extern_classes::compile_extern_method_call(
            self.ctx,
            self.builder,
            dest,
            receiver,
            class_name,
            method_name,
            is_static,
            args,
        )
    }

    // =========================================================================
    // Pattern matching
    // =========================================================================
    fn emit_pattern_test(&mut self, dest: VReg, subject: VReg, pattern: &MirPattern) -> Result<(), String> {
        super::instr::pattern::compile_pattern_test(self.ctx, self.builder, dest, subject, pattern);
        Ok(())
    }
    fn emit_pattern_bind(&mut self, dest: VReg, subject: VReg, binding: &PatternBinding) -> Result<(), String> {
        super::instr::pattern::compile_pattern_bind(self.ctx, self.builder, dest, subject, binding);
        Ok(())
    }

    // =========================================================================
    // Enums / Unions
    // =========================================================================
    fn emit_enum_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::enum_union::compile_enum_discriminant(self.ctx, self.builder, dest, value)
    }
    fn emit_enum_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::enum_union::compile_enum_payload(self.ctx, self.builder, dest, value)
    }
    fn emit_enum_unit(&mut self, dest: VReg, variant_name: &str) -> Result<(), String> {
        super::instr::pattern::compile_enum_unit(self.ctx, self.builder, dest, variant_name);
        Ok(())
    }
    fn emit_enum_with(&mut self, dest: VReg, variant_name: &str, payload: VReg) -> Result<(), String> {
        super::instr::pattern::compile_enum_with(self.ctx, self.builder, dest, variant_name, payload);
        Ok(())
    }
    fn emit_union_discriminant(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::enum_union::compile_union_discriminant(self.ctx, self.builder, dest, value)
    }
    fn emit_union_payload(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::enum_union::compile_union_payload(self.ctx, self.builder, dest, value)
    }
    fn emit_union_wrap(&mut self, dest: VReg, value: VReg, type_index: u32) -> Result<(), String> {
        super::instr::enum_union::compile_union_wrap(self.ctx, self.builder, dest, value, type_index)
    }

    // =========================================================================
    // Async / Concurrency
    // =========================================================================
    fn emit_future_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        super::instr::async_ops::compile_future_create(self.ctx, self.builder, dest, body_block);
        Ok(())
    }
    fn emit_await(&mut self, dest: VReg, future: VReg) -> Result<(), String> {
        super::instr::actors::compile_await(self.ctx, self.builder, dest, future)
    }
    fn emit_actor_spawn(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        super::instr::async_ops::compile_actor_spawn(self.ctx, self.builder, dest, body_block);
        Ok(())
    }
    fn emit_actor_send(&mut self, actor: VReg, message: VReg) -> Result<(), String> {
        super::instr::actors::compile_actor_send(self.ctx, self.builder, actor, message)
    }
    fn emit_actor_recv(&mut self, dest: VReg) -> Result<(), String> {
        super::instr::actors::compile_actor_recv(self.ctx, self.builder, dest)
    }
    fn emit_actor_join(&mut self, dest: VReg, actor: VReg) -> Result<(), String> {
        super::instr::actors::compile_actor_join(self.ctx, self.builder, dest, actor)
    }
    fn emit_actor_reply(&mut self, message: VReg) -> Result<(), String> {
        super::instr::actors::compile_actor_reply(self.ctx, self.builder, message)
    }
    fn emit_generator_create(&mut self, dest: VReg, body_block: BlockId) -> Result<(), String> {
        super::instr::async_ops::compile_generator_create(self.ctx, self.builder, dest, body_block);
        Ok(())
    }
    fn emit_yield(&mut self, value: VReg) -> Result<(), String> {
        super::instr::async_ops::compile_yield(self.ctx, self.builder, value)
    }
    fn emit_generator_next(&mut self, dest: VReg, generator: VReg) -> Result<(), String> {
        super::instr::actors::compile_generator_next(self.ctx, self.builder, dest, generator)
    }

    // =========================================================================
    // Result / Option
    // =========================================================================
    fn emit_try_unwrap(
        &mut self,
        dest: VReg,
        value: VReg,
        error_block: BlockId,
        error_dest: VReg,
    ) -> Result<(), String> {
        super::instr::result::compile_try_unwrap(self.ctx, self.builder, dest, value, error_block, error_dest);
        Ok(())
    }
    fn emit_option_some(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::result::compile_option_some(self.ctx, self.builder, dest, value);
        Ok(())
    }
    fn emit_option_none(&mut self, dest: VReg) -> Result<(), String> {
        super::instr::result::compile_option_none(self.ctx, self.builder, dest);
        Ok(())
    }
    fn emit_result_ok(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::result::compile_result_ok(self.ctx, self.builder, dest, value);
        Ok(())
    }
    fn emit_result_err(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::result::compile_result_err(self.ctx, self.builder, dest, value);
        Ok(())
    }

    // =========================================================================
    // Contracts
    // =========================================================================
    fn emit_contract_check(
        &mut self,
        condition: VReg,
        kind: ContractKind,
        func_name: &str,
        message: Option<&str>,
    ) -> Result<(), String> {
        super::instr::contracts::compile_contract_check(self.ctx, self.builder, condition, kind, func_name, message)
    }
    fn emit_contract_old_capture(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        super::instr::interpreter::compile_contract_old_capture(self.ctx, self.builder, dest, value)
    }

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
    ) -> Result<(), String> {
        super::instr::coverage::compile_decision_probe(self.ctx, self.builder, result, decision_id, file, line, column)
    }
    fn emit_condition_probe(
        &mut self,
        decision_id: u32,
        condition_id: u32,
        result: VReg,
        file: &str,
        line: u32,
        column: u32,
    ) -> Result<(), String> {
        super::instr::coverage::compile_condition_probe(
            self.ctx,
            self.builder,
            decision_id,
            condition_id,
            result,
            file,
            line,
            column,
        )
    }
    fn emit_path_probe(&mut self, path_id: u32, block_id: u32) -> Result<(), String> {
        super::instr::coverage::compile_path_probe(self.ctx, self.builder, path_id, block_id)
    }

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
    ) -> Result<(), String> {
        super::instr::units::compile_unit_bound_check(self.ctx, self.builder, value, unit_name, min, max, overflow)
    }
    fn emit_unit_widen(
        &mut self,
        dest: VReg,
        value: VReg,
        from_bits: u8,
        to_bits: u8,
        signed: bool,
    ) -> Result<(), String> {
        super::instr::units::compile_unit_widen(self.ctx, self.builder, dest, value, from_bits, to_bits, signed)
    }
    fn emit_unit_narrow(
        &mut self,
        dest: VReg,
        value: VReg,
        from_bits: u8,
        to_bits: u8,
        signed: bool,
        overflow: UnitOverflowBehavior,
    ) -> Result<(), String> {
        super::instr::units::compile_unit_narrow(
            self.ctx,
            self.builder,
            dest,
            value,
            from_bits,
            to_bits,
            signed,
            overflow,
        )
    }
    fn emit_unit_saturate(&mut self, dest: VReg, value: VReg, min: i64, max: i64) -> Result<(), String> {
        super::instr::units::compile_unit_saturate(self.ctx, self.builder, dest, value, min, max)
    }

    // =========================================================================
    // Pointers
    // =========================================================================
    fn emit_pointer_new(&mut self, dest: VReg, kind: PointerKind, value: VReg) -> Result<(), String> {
        super::instr::pointers::compile_pointer_new(self.ctx, self.builder, dest, kind, value)
    }
    fn emit_pointer_ref(&mut self, dest: VReg, kind: PointerKind, source: VReg) -> Result<(), String> {
        super::instr::pointers::compile_pointer_ref(self.ctx, self.builder, dest, kind, source)
    }
    fn emit_pointer_deref(&mut self, dest: VReg, pointer: VReg, kind: PointerKind) -> Result<(), String> {
        super::instr::pointers::compile_pointer_deref(self.ctx, self.builder, dest, pointer, kind)
    }

    // =========================================================================
    // Memory safety
    // =========================================================================
    fn emit_drop(&mut self, _value: VReg, _ty: TypeId) -> Result<(), String> {
        // Same no-op as existing compile_instruction
        Ok(())
    }
    fn emit_end_scope(&mut self, _local_index: usize) -> Result<(), String> {
        Ok(())
    }

    // =========================================================================
    // Boxing
    // =========================================================================
    fn emit_box_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let mut val = self
            .ctx
            .vreg_values
            .get(&value)
            .copied()
            .unwrap_or_else(|| self.builder.ins().iconst(types::I64, 0));
        let val_type = self.builder.func.dfg.value_type(val);
        if val_type == types::I32 || val_type == types::I8 || val_type == types::I16 {
            val = self.builder.ins().sextend(types::I64, val);
        }
        let three = self.builder.ins().iconst(types::I64, 3);
        let boxed = self.builder.ins().ishl(val, three);
        self.ctx.vreg_values.insert(dest, boxed);
        Ok(())
    }
    fn emit_box_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self
            .ctx
            .vreg_values
            .get(&value)
            .copied()
            .unwrap_or_else(|| self.builder.ins().f64const(0.0));
        let bits = self.builder.ins().bitcast(types::I64, MemFlags::new(), val);
        let three = self.builder.ins().iconst(types::I64, 3);
        let shifted = self.builder.ins().ushr(bits, three);
        let payload = self.builder.ins().ishl(shifted, three);
        let tag = self.builder.ins().iconst(types::I64, 2);
        let boxed = self.builder.ins().bor(payload, tag);
        self.ctx.vreg_values.insert(dest, boxed);
        Ok(())
    }
    fn emit_unbox_int(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self
            .ctx
            .vreg_values
            .get(&value)
            .copied()
            .unwrap_or_else(|| self.builder.ins().iconst(types::I64, 0));
        let three = self.builder.ins().iconst(types::I64, 3);
        let unboxed = self.builder.ins().sshr(val, three);
        self.ctx.vreg_values.insert(dest, unboxed);
        Ok(())
    }
    fn emit_unbox_float(&mut self, dest: VReg, value: VReg) -> Result<(), String> {
        let val = self
            .ctx
            .vreg_values
            .get(&value)
            .copied()
            .unwrap_or_else(|| self.builder.ins().iconst(types::I64, 0));
        let three = self.builder.ins().iconst(types::I64, 3);
        let shifted = self.builder.ins().ushr(val, three);
        let bits = self.builder.ins().ishl(shifted, three);
        let unboxed = self.builder.ins().bitcast(types::F64, MemFlags::new(), bits);
        self.ctx.vreg_values.insert(dest, unboxed);
        Ok(())
    }

    // =========================================================================
    // GPU
    // =========================================================================
    fn emit_gpu_global_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_global_id(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_local_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_local_id(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_group_id(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_group_id(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_global_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_global_size(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_local_size(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_local_size(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_num_groups(&mut self, dest: VReg, dim: u8) -> Result<(), String> {
        super::instr_gpu::compile_gpu_num_groups(self.ctx, self.builder, dest, dim)
    }
    fn emit_gpu_barrier(&mut self) -> Result<(), String> {
        super::instr_gpu::compile_gpu_barrier(self.ctx, self.builder)
    }
    fn emit_gpu_mem_fence(&mut self, scope: GpuMemoryScope) -> Result<(), String> {
        super::instr_gpu::compile_gpu_mem_fence(self.ctx, self.builder, scope)
    }
    fn emit_gpu_shared_alloc(&mut self, dest: VReg, element_type: TypeId, size: u32) -> Result<(), String> {
        super::instr_gpu::compile_gpu_shared_alloc(self.ctx, self.builder, dest, element_type, size)
    }
    fn emit_gpu_atomic(&mut self, dest: VReg, op: GpuAtomicOp, ptr: VReg, value: VReg) -> Result<(), String> {
        super::instr::collections::compile_gpu_atomic(self.ctx, self.builder, dest, op, ptr, value);
        Ok(())
    }
    fn emit_gpu_atomic_cmpxchg(&mut self, dest: VReg, ptr: VReg, expected: VReg, desired: VReg) -> Result<(), String> {
        super::instr::collections::compile_gpu_atomic_cmpxchg(self.ctx, self.builder, dest, ptr, expected, desired);
        Ok(())
    }

    // =========================================================================
    // Parallel iterators
    // =========================================================================
    fn emit_par_map(
        &mut self,
        dest: VReg,
        input: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        super::instr::parallel::compile_par_map(self.ctx, self.builder, dest, input, closure, backend)
    }
    fn emit_par_reduce(
        &mut self,
        dest: VReg,
        input: VReg,
        initial: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        super::instr::parallel::compile_par_reduce(self.ctx, self.builder, dest, input, initial, closure, backend)
    }
    fn emit_par_filter(
        &mut self,
        dest: VReg,
        input: VReg,
        predicate: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        super::instr::parallel::compile_par_filter(self.ctx, self.builder, dest, input, predicate, backend)
    }
    fn emit_par_for_each(
        &mut self,
        input: VReg,
        closure: VReg,
        backend: Option<ParallelBackend>,
    ) -> Result<(), String> {
        super::instr::parallel::compile_par_for_each(self.ctx, self.builder, input, closure, backend)
    }
}
