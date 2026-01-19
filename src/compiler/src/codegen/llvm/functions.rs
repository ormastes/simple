/// LLVM function compilation - main compile_function implementation
///
/// This module orchestrates MIR function compilation to LLVM IR by dispatching
/// instructions to specialized helper methods organized by category.
use super::LlvmBackend;
use crate::error::CompileError;
use crate::mir::MirFunction;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

mod calls;
mod casts;
mod collections;
mod consts;
mod memory;
mod objects;

/// Type alias for vreg map
#[cfg(feature = "llvm")]
type VRegMap = std::collections::HashMap<crate::mir::VReg, inkwell::values::BasicValueEnum<'static>>;

/// Fallback VRegMap when LLVM is not enabled
#[cfg(not(feature = "llvm"))]
type VRegMap = std::collections::HashMap<crate::mir::VReg, ()>;

impl LlvmBackend {
    /// Compile a MIR function to LLVM IR (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_function(&self, func: &MirFunction) -> Result<(), CompileError> {
        use crate::hir::TypeId;
        use std::collections::HashMap;

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;

        // Get the function that was forward-declared in the compile() pass
        // If it doesn't exist, create it (for backwards compatibility)
        let function = module.get_function(&func.name).unwrap_or_else(|| {
            // Map parameter types
            let param_types: Vec<_> = func
                .params
                .iter()
                .filter_map(|p| self.llvm_type(&p.ty).ok().map(|t| t.into()))
                .collect();

            // Create function type
            let fn_type = if func.return_type == TypeId::VOID {
                self.context.void_type().fn_type(&param_types, false)
            } else if let Ok(ret_llvm) = self.llvm_type(&func.return_type) {
                match ret_llvm {
                    BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
                    BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
                    BasicTypeEnum::PointerType(t) => t.fn_type(&param_types, false),
                    _ => self.context.i64_type().fn_type(&param_types, false),
                }
            } else {
                self.context.i64_type().fn_type(&param_types, false)
            };

            module.add_function(&func.name, fn_type, None)
        });

        // Create basic blocks for each MIR block
        let mut llvm_blocks = HashMap::new();
        for block in &func.blocks {
            let bb = self.context.append_basic_block(function, &format!("bb{}", block.id.0));
            llvm_blocks.insert(block.id, bb);
        }

        // Map virtual registers to LLVM values
        let mut vreg_map: VRegMap = HashMap::new();

        // Allocate stack space for parameters and locals at the entry block
        // Parameters and locals share a combined index space: params at 0..param_count, locals at param_count..
        let mut local_allocas: HashMap<usize, inkwell::values::PointerValue<'static>> = HashMap::new();
        if !func.blocks.is_empty() {
            let entry_bb = llvm_blocks[&func.blocks[0].id];
            builder.position_at_end(entry_bb);

            // Create allocas for parameters (index 0..param_count)
            for (i, param) in func.params.iter().enumerate() {
                let param_ty = self.llvm_type(&param.ty)?;
                let alloca = builder
                    .build_alloca(param_ty, &param.name)
                    .map_err(|e| crate::error::factory::llvm_build_failed("param alloca", &e))?;
                local_allocas.insert(i, alloca);
            }

            // Create allocas for locals (index param_count..param_count+local_count)
            let param_count = func.params.len();
            for (i, local) in func.locals.iter().enumerate() {
                let local_ty = self.llvm_type(&local.ty)?;
                let alloca = builder
                    .build_alloca(local_ty, &local.name)
                    .map_err(|e| crate::error::factory::llvm_build_failed("local alloca", &e))?;
                local_allocas.insert(param_count + i, alloca);
            }

            // Store parameter values into their allocas
            for (i, _param) in func.params.iter().enumerate() {
                if let Some(llvm_param) = function.get_nth_param(i as u32) {
                    if let Some(&alloca) = local_allocas.get(&i) {
                        builder
                            .build_store(alloca, llvm_param)
                            .map_err(|e| CompileError::Semantic(format!("Failed to store param: {}", e)))?;
                    }
                }
            }
        }

        // Map function parameters to virtual registers (for direct use before LocalAddr/Load)
        for (i, _param) in func.params.iter().enumerate() {
            if let Some(llvm_param) = function.get_nth_param(i as u32) {
                // Params are mapped to vregs starting from VReg(0)
                vreg_map.insert(crate::mir::VReg(i as u32), llvm_param.into());
            }
        }

        // Compile each block
        for block in &func.blocks {
            let bb = llvm_blocks[&block.id];
            builder.position_at_end(bb);

            // Emit coverage counter increment if coverage is enabled
            if self.coverage_enabled {
                self.emit_coverage_counter(module, builder, &func.name, block.id.0)?;
            }

            // Compile each instruction by dispatching to helper methods
            for inst in &block.instructions {
                self.compile_instruction(inst, &mut vreg_map, &local_allocas, builder, module)?;
            }

            // Compile terminator
            self.compile_terminator(&block.terminator, &llvm_blocks, &vreg_map, builder)?;
        }

        Ok(())
    }

    /// Compile a single MIR instruction by dispatching to category-specific helpers
    #[cfg(feature = "llvm")]
    fn compile_instruction(
        &self,
        inst: &crate::mir::MirInst,
        vreg_map: &mut VRegMap,
        local_allocas: &std::collections::HashMap<usize, inkwell::values::PointerValue<'static>>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use crate::mir::MirInst;

        match inst {
            // Constants
            MirInst::ConstInt { dest, value } => {
                self.compile_const_int(*dest, *value, vreg_map)?;
            }
            MirInst::ConstBool { dest, value } => {
                self.compile_const_bool(*dest, *value, vreg_map)?;
            }
            MirInst::ConstFloat { dest, value } => {
                self.compile_const_float(*dest, *value, vreg_map)?;
            }
            MirInst::ConstString { dest, value } => {
                self.compile_const_string(*dest, value, vreg_map, module)?;
            }
            MirInst::ConstSymbol { dest, value } => {
                self.compile_const_symbol(*dest, value, vreg_map, module)?;
            }

            // Arithmetic & basic ops (delegates to existing methods)
            MirInst::Copy { dest, src } => {
                if let Some(val) = vreg_map.get(src) {
                    vreg_map.insert(*dest, *val);
                }
            }
            MirInst::BinOp { dest, op, left, right } => {
                let left_val = self.get_vreg(left, vreg_map)?;
                let right_val = self.get_vreg(right, vreg_map)?;
                let result = self.compile_binop(*op, left_val, right_val, builder)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::UnaryOp { dest, op, operand } => {
                let operand_val = self.get_vreg(operand, vreg_map)?;
                let result = self.compile_unaryop(*op, operand_val, builder)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::Cast {
                dest,
                source,
                from_ty,
                to_ty,
            } => {
                let source_val = self.get_vreg(source, vreg_map)?;
                let result = self.compile_cast(source_val, from_ty, to_ty, builder)?;
                vreg_map.insert(*dest, result);
            }

            // Memory
            MirInst::Load { dest, addr, ty } => {
                self.compile_load(*dest, *addr, ty, vreg_map, builder)?;
            }
            MirInst::Store { addr, value, ty } => {
                self.compile_store(*addr, *value, ty, vreg_map, builder)?;
            }
            MirInst::GcAlloc { dest, ty } => {
                self.compile_gc_alloc(*dest, ty, vreg_map, builder)?;
            }
            MirInst::LocalAddr { dest, local_index } => {
                let alloca = local_allocas
                    .get(local_index)
                    .ok_or_else(|| CompileError::Semantic(format!("Unknown local index: {}", local_index)))?;
                vreg_map.insert(*dest, (*alloca).into());
            }

            // Collections
            MirInst::ArrayLit { dest, elements } => {
                self.compile_array_lit(*dest, elements, vreg_map, builder)?;
            }
            MirInst::TupleLit { dest, elements } => {
                self.compile_tuple_lit(*dest, elements, vreg_map, builder)?;
            }
            MirInst::DictLit { dest, keys, values } => {
                self.compile_dict_lit(*dest, keys, values, vreg_map, builder, module)?;
            }
            MirInst::IndexGet {
                dest,
                collection,
                index,
            } => {
                self.compile_index_get(*dest, *collection, *index, vreg_map, builder)?;
            }
            MirInst::IndexSet {
                collection,
                index,
                value,
            } => {
                self.compile_index_set(*collection, *index, *value, vreg_map, builder)?;
            }
            MirInst::SliceOp {
                dest,
                collection,
                start,
                end,
                step,
            } => {
                self.compile_slice_op(*dest, *collection, *start, *end, *step, vreg_map, builder, module)?;
            }

            // Calls
            MirInst::Call { dest, target, args } => {
                self.compile_call(*dest, target, args, vreg_map, builder, module)?;
            }
            MirInst::IndirectCall {
                dest,
                callee,
                param_types,
                return_type,
                args,
                ..
            } => {
                self.compile_indirect_call(*dest, *callee, param_types, return_type, args, vreg_map, builder)?;
            }
            MirInst::InterpCall { dest, func_name, args } => {
                self.compile_interp_call(*dest, func_name, args, vreg_map, builder, module)?;
            }
            MirInst::InterpEval { dest, expr_index } => {
                self.compile_interp_eval(*dest, *expr_index as usize, vreg_map, builder, module)?;
            }

            // Objects
            MirInst::StructInit {
                dest,
                struct_size,
                field_offsets,
                field_types,
                field_values,
                ..
            } => {
                self.compile_struct_init(
                    *dest,
                    *struct_size,
                    field_offsets,
                    field_types,
                    field_values,
                    vreg_map,
                    builder,
                )?;
            }
            MirInst::FieldGet {
                dest,
                object,
                byte_offset,
                field_type,
            } => {
                self.compile_field_get(*dest, *object, *byte_offset, field_type, vreg_map, builder)?;
            }
            MirInst::FieldSet {
                object,
                byte_offset,
                field_type,
                value,
            } => {
                self.compile_field_set(*object, *byte_offset, field_type, *value, vreg_map, builder)?;
            }
            MirInst::ClosureCreate {
                dest,
                func_name,
                closure_size,
                capture_offsets,
                capture_types,
                captures,
            } => {
                self.compile_closure_create(
                    *dest,
                    func_name,
                    *closure_size,
                    capture_offsets,
                    capture_types,
                    captures,
                    vreg_map,
                    builder,
                    module,
                )?;
            }

            // GPU instructions (delegates to gpu_instructions.rs)
            MirInst::GpuGlobalId { dest, dim } => {
                let result = self.compile_gpu_global_id(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuLocalId { dest, dim } => {
                let result = self.compile_gpu_local_id(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuGroupId { dest, dim } => {
                let result = self.compile_gpu_group_id(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuGlobalSize { dest, dim } => {
                let result = self.compile_gpu_global_size(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuLocalSize { dest, dim } => {
                let result = self.compile_gpu_local_size(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuNumGroups { dest, dim } => {
                let result = self.compile_gpu_num_groups(*dim, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuBarrier => {
                self.compile_gpu_barrier(builder, module)?;
            }
            MirInst::GpuMemFence { scope } => {
                self.compile_gpu_mem_fence(*scope, builder, module)?;
            }
            MirInst::GpuAtomic { dest, op, ptr, value } => {
                let ptr_val = self.get_vreg(ptr, vreg_map)?;
                let value_val = self.get_vreg(value, vreg_map)?;
                let result = self.compile_gpu_atomic(*op, ptr_val, value_val, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuAtomicCmpXchg {
                dest,
                ptr,
                expected,
                desired,
            } => {
                let ptr_val = self.get_vreg(ptr, vreg_map)?;
                let expected_val = self.get_vreg(expected, vreg_map)?;
                let desired_val = self.get_vreg(desired, vreg_map)?;
                let result = self.compile_gpu_atomic_cmpxchg(ptr_val, expected_val, desired_val, builder, module)?;
                vreg_map.insert(*dest, result);
            }
            MirInst::GpuSharedAlloc { dest, size, .. } => {
                let result = self.compile_gpu_shared_alloc(*size, builder, module)?;
                vreg_map.insert(*dest, result);
            }

            _ => {
                // Other instructions not yet implemented
            }
        }

        Ok(())
    }

    // ============================================================================
    // Helper: VReg access
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn get_vreg(
        &self,
        vreg: &crate::mir::VReg,
        vreg_map: &VRegMap,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        vreg_map
            .get(vreg)
            .copied()
            .ok_or_else(|| CompileError::Semantic(format!("Undefined vreg: {:?}", vreg)))
    }
}

// ============================================================================
// Stub implementation for non-LLVM builds
// ============================================================================

#[cfg(not(feature = "llvm"))]
impl LlvmBackend {
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }
}
