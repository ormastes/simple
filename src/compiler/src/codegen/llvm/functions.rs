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

/// Type alias for vreg map
#[cfg(feature = "llvm")]
type VRegMap = std::collections::HashMap<crate::mir::VReg, inkwell::values::BasicValueEnum<'static>>;

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
            let bb = self
                .context
                .append_basic_block(function, &format!("bb{}", block.id.0));
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
                    .map_err(|e| CompileError::Semantic(format!("Failed to build param alloca: {}", e)))?;
                local_allocas.insert(i, alloca);
            }

            // Create allocas for locals (index param_count..param_count+local_count)
            let param_count = func.params.len();
            for (i, local) in func.locals.iter().enumerate() {
                let local_ty = self.llvm_type(&local.ty)?;
                let alloca = builder
                    .build_alloca(local_ty, &local.name)
                    .map_err(|e| CompileError::Semantic(format!("Failed to build local alloca: {}", e)))?;
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
            MirInst::BinOp {
                dest,
                op,
                left,
                right,
            } => {
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
            MirInst::Cast { dest, source, from_ty, to_ty } => {
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
                let alloca = local_allocas.get(local_index)
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
            MirInst::InterpCall {
                dest,
                func_name,
                args,
            } => {
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
                self.compile_struct_init(*dest, *struct_size, field_offsets, field_types, field_values, vreg_map, builder)?;
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
                self.compile_closure_create(*dest, func_name, *closure_size, capture_offsets, capture_types, captures, vreg_map, builder, module)?;
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
            MirInst::GpuAtomicCmpXchg { dest, ptr, expected, desired } => {
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

    // ============================================================================
    // Constant Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_const_int(
        &self,
        dest: crate::mir::VReg,
        value: i64,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.i64_type().const_int(value as u64, true);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_const_bool(
        &self,
        dest: crate::mir::VReg,
        value: bool,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.bool_type().const_int(value as u64, false);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_const_float(
        &self,
        dest: crate::mir::VReg,
        value: f64,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.f64_type().const_float(value);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_const_string(
        &self,
        dest: crate::mir::VReg,
        value: &str,
        vreg_map: &mut VRegMap,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Create global string constant
        let str_val = self.context.const_string(value.as_bytes(), false);
        let global = module.add_global(str_val.get_type(), None, "str");
        global.set_initializer(&str_val);
        global.set_constant(true);
        vreg_map.insert(dest, global.as_pointer_value().into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_const_symbol(
        &self,
        dest: crate::mir::VReg,
        value: &str,
        vreg_map: &mut VRegMap,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Symbols are represented as interned string pointers
        let str_val = self.context.const_string(value.as_bytes(), false);
        let global = module.add_global(str_val.get_type(), None, &format!("sym_{}", value));
        global.set_initializer(&str_val);
        global.set_constant(true);
        vreg_map.insert(dest, global.as_pointer_value().into());
        Ok(())
    }

    // ============================================================================
    // Cast Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_cast(
        &self,
        source_val: inkwell::values::BasicValueEnum<'static>,
        from_type: &crate::hir::TypeId,
        to_type: &crate::hir::TypeId,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::TypeId;

        let i64_type = self.context.i64_type();
        let f64_type = self.context.f64_type();

        match (*from_type, *to_type) {
            // Float to Int (f64 -> i64)
            (TypeId::F64, TypeId::I64) | (TypeId::F32, TypeId::I64) | (TypeId::F32, TypeId::I32) | (TypeId::F64, TypeId::I32) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let result = builder
                        .build_float_to_signed_int(float_val, i64_type, "cast_f2i")
                        .map_err(|e| CompileError::Semantic(format!("Failed to cast float to int: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected float value for float-to-int cast".to_string()))
                }
            }
            // Int to Float (i64 -> f64)
            (TypeId::I64, TypeId::F64) | (TypeId::I32, TypeId::F64) | (TypeId::I32, TypeId::F32) | (TypeId::I64, TypeId::F32) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let result = builder
                        .build_signed_int_to_float(int_val, f64_type, "cast_i2f")
                        .map_err(|e| CompileError::Semantic(format!("Failed to cast int to float: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected int value for int-to-float cast".to_string()))
                }
            }
            // Int to Int (widening or truncation)
            (TypeId::I32, TypeId::I64) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let result = builder
                        .build_int_s_extend(int_val, i64_type, "cast_i32_i64")
                        .map_err(|e| CompileError::Semantic(format!("Failed to extend int: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected int value for int-to-int cast".to_string()))
                }
            }
            (TypeId::I64, TypeId::I32) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let i32_type = self.context.i32_type();
                    let result = builder
                        .build_int_truncate(int_val, i32_type, "cast_i64_i32")
                        .map_err(|e| CompileError::Semantic(format!("Failed to truncate int: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected int value for int-to-int cast".to_string()))
                }
            }
            // Float to Float (widening or truncation)
            (TypeId::F32, TypeId::F64) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let result = builder
                        .build_float_ext(float_val, f64_type, "cast_f32_f64")
                        .map_err(|e| CompileError::Semantic(format!("Failed to extend float: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected float value for float-to-float cast".to_string()))
                }
            }
            (TypeId::F64, TypeId::F32) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let f32_type = self.context.f32_type();
                    let result = builder
                        .build_float_trunc(float_val, f32_type, "cast_f64_f32")
                        .map_err(|e| CompileError::Semantic(format!("Failed to truncate float: {}", e)))?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic("Expected float value for float-to-float cast".to_string()))
                }
            }
            // Same type - no-op
            _ if from_type == to_type => Ok(source_val),
            // Unsupported cast
            _ => Err(CompileError::Semantic(format!(
                "Unsupported cast from {:?} to {:?}", from_type, to_type
            ))),
        }
    }

    // ============================================================================
    // Memory Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_load(
        &self,
        dest: crate::mir::VReg,
        addr: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
            let loaded = builder
                .build_load(self.llvm_type(ty)?, ptr, "load")
                .map_err(|e| CompileError::Semantic(format!("Failed to build load: {}", e)))?;
            vreg_map.insert(dest, loaded);
            Ok(())
        } else {
            Err(CompileError::Semantic("Load requires pointer".to_string()))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_store(
        &self,
        addr: crate::mir::VReg,
        value: crate::mir::VReg,
        _ty: &crate::hir::TypeId,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;
        let value_val = self.get_vreg(&value, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
            builder
                .build_store(ptr, value_val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
            Ok(())
        } else {
            Err(CompileError::Semantic(
                "Store requires pointer".to_string(),
            ))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_gc_alloc(
        &self,
        dest: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Allocate on stack for now (proper GC integration later)
        let llvm_ty = self.llvm_type(ty)?;
        let alloc = builder
            .build_alloca(llvm_ty, "gc_alloc")
            .map_err(|e| CompileError::Semantic(format!("Failed to build alloca: {}", e)))?;
        vreg_map.insert(dest, alloc.into());
        Ok(())
    }

    // ============================================================================
    // Collection Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_array_lit(
        &self,
        dest: crate::mir::VReg,
        elements: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Create array on stack and initialize elements
        let i64_type = self.context.i64_type();
        let array_type = i64_type.array_type(elements.len() as u32);
        let alloc = builder
            .build_alloca(array_type, "array")
            .map_err(|e| CompileError::Semantic(format!("Failed to build alloca: {}", e)))?;

        // Store each element
        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get_vreg(elem, vreg_map)?;

            let indices = [
                self.context.i32_type().const_int(0, false),
                self.context.i32_type().const_int(i as u64, false),
            ];
            let gep = unsafe { builder.build_gep(array_type, alloc, &indices, "elem_ptr") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;

            builder
                .build_store(gep, elem_val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
        }

        vreg_map.insert(dest, alloc.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_tuple_lit(
        &self,
        dest: crate::mir::VReg,
        elements: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Tuples are similar to arrays - create struct on stack
        let i64_type = self.context.i64_type();
        let field_types: Vec<BasicTypeEnum> = elements.iter().map(|_| i64_type.into()).collect();
        let struct_type = self.context.struct_type(&field_types, false);
        let alloc = builder
            .build_alloca(struct_type, "tuple")
            .map_err(|e| CompileError::Semantic(format!("Failed to build alloca: {}", e)))?;

        // Store each element
        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get_vreg(elem, vreg_map)?;

            let gep = builder
                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                .map_err(|e| CompileError::Semantic(format!("Failed to build struct gep: {}", e)))?;

            builder
                .build_store(gep, elem_val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
        }

        vreg_map.insert(dest, alloc.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_dict_lit(
        &self,
        dest: crate::mir::VReg,
        keys: &[crate::mir::VReg],
        values: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Dictionaries are represented as a struct with keys array and values array
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_dict_new if not exists
        let dict_new = module.get_function("rt_dict_new").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_dict_new", fn_type, None)
        });

        // Declare rt_dict_insert if not exists
        let dict_insert = module.get_function("rt_dict_insert").unwrap_or_else(|| {
            let fn_type = self.context.void_type().fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            module.add_function("rt_dict_insert", fn_type, None)
        });

        // Create new dict with initial capacity
        let capacity = i64_type.const_int(keys.len() as u64, false);
        let dict_ptr = builder
            .build_call(dict_new, &[capacity.into()], "dict")
            .map_err(|e| CompileError::Semantic(format!("Failed to build dict_new call: {}", e)))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("dict_new returned void".to_string()))?;

        // Insert each key-value pair
        for (key, value) in keys.iter().zip(values.iter()) {
            let key_val = self.get_vreg(key, vreg_map)?;
            let value_val = self.get_vreg(value, vreg_map)?;

            builder
                .build_call(
                    dict_insert,
                    &[dict_ptr.into(), key_val.into(), value_val.into()],
                    "",
                )
                .map_err(|e| {
                    CompileError::Semantic(format!("Failed to build dict_insert call: {}", e))
                })?;
        }

        vreg_map.insert(dest, dict_ptr);
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_index_get(
        &self,
        dest: crate::mir::VReg,
        collection: crate::mir::VReg,
        index: crate::mir::VReg,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;

        // Collection should be a pointer to array
        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                let i64_type = self.context.i64_type();
                let arr_type = i64_type.array_type(0); // Dynamic size

                let indices = [self.context.i32_type().const_int(0, false), idx];
                let gep = unsafe { builder.build_gep(arr_type, ptr, &indices, "elem_ptr") }
                    .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;

                let loaded = builder
                    .build_load(i64_type, gep, "elem")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build load: {}", e)))?;

                vreg_map.insert(dest, loaded);
            }
        }
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_index_set(
        &self,
        collection: crate::mir::VReg,
        index: crate::mir::VReg,
        value: crate::mir::VReg,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;
        let val = self.get_vreg(&value, vreg_map)?;

        // Collection should be a pointer to array
        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                let i64_type = self.context.i64_type();
                let arr_type = i64_type.array_type(0);

                let indices = [self.context.i32_type().const_int(0, false), idx];
                let gep = unsafe { builder.build_gep(arr_type, ptr, &indices, "elem_ptr") }
                    .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;

                builder
                    .build_store(gep, val)
                    .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
            }
        }
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_slice_op(
        &self,
        dest: crate::mir::VReg,
        collection: crate::mir::VReg,
        start: Option<crate::mir::VReg>,
        end: Option<crate::mir::VReg>,
        step: Option<crate::mir::VReg>,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_slice if not exists
        let slice_fn = module.get_function("rt_slice").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(
                &[
                    i8_ptr_type.into(),
                    i64_type.into(),
                    i64_type.into(),
                    i64_type.into(),
                ],
                false,
            );
            module.add_function("rt_slice", fn_type, None)
        });

        let coll_val = self.get_vreg(&collection, vreg_map)?;

        // Get start index (default to 0 if None)
        let start_val = if let Some(s) = start {
            self.get_vreg(&s, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(0, false))
        };

        // Get end index (default to -1 meaning end of collection)
        let end_val = if let Some(e) = end {
            self.get_vreg(&e, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(i64::MAX as u64, false))
        };

        // Get step (default to 1)
        let step_val = if let Some(s) = step {
            self.get_vreg(&s, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(1, false))
        };

        let call_site = builder
            .build_call(
                slice_fn,
                &[
                    coll_val.into(),
                    start_val.into(),
                    end_val.into(),
                    step_val.into(),
                ],
                "slice",
            )
            .map_err(|e| CompileError::Semantic(format!("Failed to build slice call: {}", e)))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        }

        Ok(())
    }

    // ============================================================================
    // Call Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_call(
        &self,
        dest: Option<crate::mir::VReg>,
        target: &crate::mir::CallTarget,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Get or declare the called function
        let func_name = target.name();
        let called_func = module.get_function(func_name).ok_or_else(|| {
            // Function not found, try to declare it
            // For now, assume all functions return i64 and take i64 params
            let i64_type = self.context.i64_type();
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(func_name, fn_type, None)
        });

        let called_func = match called_func {
            Ok(f) => f,
            Err(f) => f, // Use the declared function
        };

        // Collect argument values
        let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
        for arg in args {
            let val = self.get_vreg(arg, vreg_map)?;
            arg_vals.push(val.into());
        }

        // Build the call
        let call_site = builder
            .build_call(called_func, &arg_vals, "call")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        // Store result if there's a destination
        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_indirect_call(
        &self,
        dest: Option<crate::mir::VReg>,
        callee: crate::mir::VReg,
        param_types: &[crate::hir::TypeId],
        return_type: &crate::hir::TypeId,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        use crate::hir::TypeId;

        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        let callee_val = self.get_vreg(&callee, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(closure_ptr) = callee_val {
            let base_ptr = builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| CompileError::Semantic(format!("Failed to cast closure ptr: {}", e)))?;

            let offset_val = self.context.i32_type().const_int(0, false);
            let fn_ptr_slot = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;

            let fn_ptr_slot = builder
                .build_pointer_cast(
                    fn_ptr_slot,
                    i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                    "fn_ptr_slot_cast",
                )
                .map_err(|e| CompileError::Semantic(format!("Failed to cast fn slot ptr: {}", e)))?;

            let func_ptr = builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| CompileError::Semantic(format!("Failed to build load: {}", e)))?;

            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    arg_vals.push(val.into());
                }

                let llvm_param_types: Result<Vec<inkwell::types::BasicMetadataTypeEnum>, CompileError> =
                    param_types.iter().map(|ty| self.llvm_type(ty).map(|t| t.into())).collect();
                let llvm_param_types = llvm_param_types?;

                let fn_type = if *return_type == TypeId::VOID {
                    self.context.void_type().fn_type(&llvm_param_types, false)
                } else {
                    let ret_llvm = self.llvm_type(return_type)?;
                    match ret_llvm {
                        BasicTypeEnum::IntType(t) => t.fn_type(&llvm_param_types, false),
                        BasicTypeEnum::FloatType(t) => t.fn_type(&llvm_param_types, false),
                        BasicTypeEnum::PointerType(t) => t.fn_type(&llvm_param_types, false),
                        _ => {
                            return Err(CompileError::Semantic(
                                "Unsupported return type".to_string(),
                            ))
                        }
                    }
                };

                let call_site = builder
                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                    .map_err(|e| {
                        CompileError::Semantic(format!("Failed to build indirect call: {}", e))
                    })?;

                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(d, ret_val);
                    }
                }
            }
        } else {
            return Err(CompileError::Semantic(
                "IndirectCall requires closure pointer".to_string(),
            ));
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_interp_call(
        &self,
        dest: Option<crate::mir::VReg>,
        func_name: &str,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Call interpreter bridge function rt_interp_call
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_interp_call if not exists
        let interp_call = module.get_function("rt_interp_call").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[
                    i8_ptr_type.into(),
                    i64_type.into(),
                    i64_type.into(),
                    i8_ptr_type.into(),
                ],
                false,
            );
            module.add_function("rt_interp_call", fn_type, None)
        });

        // Create string constant for function name
        let name_bytes = func_name.as_bytes();
        let name_const = self.context.const_string(name_bytes, false);
        let name_global = module.add_global(name_const.get_type(), None, "func_name");
        name_global.set_initializer(&name_const);
        name_global.set_constant(true);
        let name_ptr = name_global.as_pointer_value();
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);

        // For now, pass null for args array (simplified)
        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = i8_ptr_type.const_null();

        let call_args = [
            name_ptr.into(),
            name_len.into(),
            argc.into(),
            argv.into(),
        ];

        let call_site = builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_interp_eval(
        &self,
        dest: crate::mir::VReg,
        expr_index: usize,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Call interpreter to evaluate expression by index
        let i64_type = self.context.i64_type();

        // Declare rt_interp_eval if not exists
        let interp_eval = module.get_function("rt_interp_eval").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_interp_eval", fn_type, None)
        });

        let expr_index_val = i64_type.const_int(expr_index as u64, true);
        let call_site = builder
            .build_call(interp_eval, &[expr_index_val.into()], "eval")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        }

        Ok(())
    }

    // ============================================================================
    // Object Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_struct_init(
        &self,
        dest: crate::mir::VReg,
        struct_size: u32,
        field_offsets: &[u32],
        field_types: &[crate::hir::TypeId],
        field_values: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(struct_size);
        let alloc = builder
            .build_alloca(array_type, "struct")
            .map_err(|e| CompileError::Semantic(format!("Failed to build alloca: {}", e)))?;
        let struct_ptr = builder
            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
            .map_err(|e| CompileError::Semantic(format!("Failed to cast struct ptr: {}", e)))?;

        for ((offset, field_type), value) in field_offsets
            .iter()
            .zip(field_types.iter())
            .zip(field_values.iter())
        {
            let field_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| CompileError::Semantic(format!("Failed to cast field ptr: {}", e)))?;
            builder
                .build_store(typed_ptr, field_val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
        }

        vreg_map.insert(dest, struct_ptr.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_field_get(
        &self,
        dest: crate::mir::VReg,
        object: crate::mir::VReg,
        byte_offset: u32,
        field_type: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let obj_val = self.get_vreg(&object, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.context.i8_type();
            let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
            let base_ptr = builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| CompileError::Semantic(format!("Failed to cast struct ptr: {}", e)))?;
            let offset_val = self.context.i32_type().const_int(byte_offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| CompileError::Semantic(format!("Failed to cast field ptr: {}", e)))?;
            let loaded = builder
                .build_load(llvm_field_ty, typed_ptr, "field")
                .map_err(|e| CompileError::Semantic(format!("Failed to build load: {}", e)))?;

            vreg_map.insert(dest, loaded);
            Ok(())
        } else {
            Err(CompileError::Semantic(
                "FieldGet requires pointer to struct".to_string(),
            ))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_field_set(
        &self,
        object: crate::mir::VReg,
        byte_offset: u32,
        field_type: &crate::hir::TypeId,
        value: crate::mir::VReg,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let obj_val = self.get_vreg(&object, vreg_map)?;
        let val = self.get_vreg(&value, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.context.i8_type();
            let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
            let base_ptr = builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| CompileError::Semantic(format!("Failed to cast struct ptr: {}", e)))?;
            let offset_val = self.context.i32_type().const_int(byte_offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| CompileError::Semantic(format!("Failed to cast field ptr: {}", e)))?;
            builder
                .build_store(typed_ptr, val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
            Ok(())
        } else {
            Err(CompileError::Semantic(
                "FieldSet requires pointer to struct".to_string(),
            ))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_closure_create(
        &self,
        dest: crate::mir::VReg,
        func_name: &str,
        closure_size: u32,
        capture_offsets: &[u32],
        capture_types: &[crate::hir::TypeId],
        captures: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(closure_size);
        let alloc = builder
            .build_alloca(array_type, "closure")
            .map_err(|e| CompileError::Semantic(format!("Failed to build alloca: {}", e)))?;
        let closure_ptr = builder
            .build_pointer_cast(alloc, i8_ptr_type, "closure_ptr")
            .map_err(|e| CompileError::Semantic(format!("Failed to cast closure ptr: {}", e)))?;

        let func_ptr = module
            .get_function(func_name)
            .map(|f| f.as_global_value().as_pointer_value())
            .unwrap_or_else(|| i8_ptr_type.const_null());
        let func_ptr_cast = builder
            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
            .map_err(|e| CompileError::Semantic(format!("Failed to cast fn ptr: {}", e)))?;
        let fn_slot = builder
            .build_pointer_cast(
                closure_ptr,
                i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                "fn_slot",
            )
            .map_err(|e| CompileError::Semantic(format!("Failed to cast fn slot: {}", e)))?;
        builder
            .build_store(fn_slot, func_ptr_cast)
            .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;

        for ((offset, field_type), value) in capture_offsets
            .iter()
            .zip(capture_types.iter())
            .zip(captures.iter())
        {
            let capture_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr") }
                .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "cap_typed_ptr",
                )
                .map_err(|e| CompileError::Semantic(format!("Failed to cast cap ptr: {}", e)))?;
            builder
                .build_store(typed_ptr, capture_val)
                .map_err(|e| CompileError::Semantic(format!("Failed to build store: {}", e)))?;
        }

        vreg_map.insert(dest, closure_ptr.into());
        Ok(())
    }

    // ============================================================================
    // Stub implementation for non-LLVM builds
    // ============================================================================

    #[cfg(not(feature = "llvm"))]
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }
}
