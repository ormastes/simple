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
        use std::collections::HashSet;

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_builder_not_created)?;

        // Get the function that was forward-declared in the compile() pass
        // If it doesn't exist, create it (for backwards compatibility)
        let function = module.get_function(&func.name).unwrap_or_else(|| {
            let i64_type = self.context.i64_type();
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                func.params.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(&func.name, fn_type, None)
        });

        // Create basic blocks for each MIR block
        let mut llvm_blocks = HashMap::new();
        for block in &func.blocks {
            let bb = self.context.append_basic_block(function, &format!("bb{}", block.id.0));
            llvm_blocks.insert(block.id, bb);
        }

        // Map virtual registers to LLVM values (used within each block)
        let mut vreg_map: VRegMap = HashMap::new();

        // ======================================================================
        // Pre-allocate allocas for ALL vregs at the entry block.
        // This enables correct SSA form across basic blocks: values are stored
        // to allocas when defined and loaded when used in other blocks.
        // LLVM's mem2reg pass will optimize these back to SSA with phi nodes.
        // ======================================================================
        let mut vreg_allocas: HashMap<crate::mir::VReg, inkwell::values::PointerValue<'static>> = HashMap::new();

        // Collect all vregs used in this function
        let mut all_vregs = HashSet::new();
        for (i, _) in func.params.iter().enumerate() {
            all_vregs.insert(crate::mir::VReg(i as u32));
        }
        for block in &func.blocks {
            for inst in &block.instructions {
                if let Some(d) = inst.dest() {
                    all_vregs.insert(d);
                }
                for u in inst.uses() {
                    all_vregs.insert(u);
                }
            }
            match &block.terminator {
                crate::mir::Terminator::Return(Some(v)) => { all_vregs.insert(*v); }
                crate::mir::Terminator::Branch { cond, .. } => { all_vregs.insert(*cond); }
                _ => {}
            }
        }

        // Allocate stack space for parameters and locals at the entry block
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

            // Create allocas for all vregs (for cross-block SSA correctness)
            let i64_type = self.context.i64_type();
            for vreg in &all_vregs {
                let alloca = builder
                    .build_alloca(i64_type, &format!("v{}", vreg.0))
                    .map_err(|e| crate::error::factory::llvm_build_failed("vreg alloca", &e))?;
                // Initialize to zero
                let _ = builder.build_store(alloca, i64_type.const_int(0, false));
                vreg_allocas.insert(*vreg, alloca);
            }

            // Store parameter values into their local allocas
            for (i, _param) in func.params.iter().enumerate() {
                if let Some(llvm_param) = function.get_nth_param(i as u32) {
                    if let Some(&alloca) = local_allocas.get(&i) {
                        builder
                            .build_store(alloca, llvm_param)
                            .map_err(|e| crate::error::factory::llvm_build_failed("store param", &e))?;
                    }
                    // Also store param to vreg alloca
                    let vreg = crate::mir::VReg(i as u32);
                    if let Some(&va) = vreg_allocas.get(&vreg) {
                        let _ = builder.build_store(va, llvm_param);
                    }
                }
            }
        }

        // Map function parameters to virtual registers
        for (i, _param) in func.params.iter().enumerate() {
            if let Some(llvm_param) = function.get_nth_param(i as u32) {
                vreg_map.insert(crate::mir::VReg(i as u32), llvm_param.into());
            }
        }

        let is_entry_block_id = func.blocks.first().map(|b| b.id);

        // Compile each block
        for block in &func.blocks {
            let bb = llvm_blocks[&block.id];
            builder.position_at_end(bb);

            // At the start of each non-entry block, reload only the vregs that are
            // used in this block but not defined in it (live-in set).
            // This fixes SSA dominance without the O(num_vregs) penalty per block.
            if Some(block.id) != is_entry_block_id {
                vreg_map.clear();

                // Compute vregs defined in this block
                let mut block_defs = HashSet::new();
                for inst in &block.instructions {
                    if let Some(d) = inst.dest() {
                        block_defs.insert(d);
                    }
                }

                // Compute vregs used in this block but not defined here (live-in)
                let mut live_in = HashSet::new();
                for inst in &block.instructions {
                    for u in inst.uses() {
                        if !block_defs.contains(&u) {
                            live_in.insert(u);
                        }
                    }
                }
                match &block.terminator {
                    crate::mir::Terminator::Return(Some(v)) => {
                        if !block_defs.contains(v) { live_in.insert(*v); }
                    }
                    crate::mir::Terminator::Branch { cond, .. } => {
                        if !block_defs.contains(cond) { live_in.insert(*cond); }
                    }
                    _ => {}
                }

                // Load only live-in vregs from allocas
                let i64_type = self.context.i64_type();
                for vreg in &live_in {
                    if let Some(&alloca) = vreg_allocas.get(vreg) {
                        if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", vreg.0)) {
                            vreg_map.insert(*vreg, val);
                        }
                    }
                }
            }

            // Emit coverage counter increment if coverage is enabled
            if self.coverage_enabled {
                self.emit_coverage_counter(module, builder, &func.name, block.id.0)?;
            }

            // Compile each instruction by dispatching to helper methods
            for inst in &block.instructions {
                self.compile_instruction(inst, &mut vreg_map, &local_allocas, builder, module)?;

                // Store any newly defined vreg to its alloca (for cross-block access)
                if let Some(d) = inst.dest() {
                    if let (Some(&alloca), Some(&val)) = (vreg_allocas.get(&d), vreg_map.get(&d)) {
                        // Coerce value to i64 before storing (alloca is i64 type)
                        let i64_type = self.context.i64_type();
                        let i64_val = match val {
                            inkwell::values::BasicValueEnum::IntValue(iv) => {
                                if iv.get_type().get_bit_width() == 64 {
                                    val
                                } else {
                                    builder.build_int_z_extend(iv, i64_type, "vext")
                                        .map(|v| v.into())
                                        .unwrap_or(val)
                                }
                            }
                            inkwell::values::BasicValueEnum::PointerValue(pv) => {
                                builder.build_ptr_to_int(pv, i64_type, "vp2i")
                                    .map(|v| v.into())
                                    .unwrap_or(val)
                            }
                            inkwell::values::BasicValueEnum::FloatValue(fv) => {
                                builder.build_float_to_signed_int(fv, i64_type, "vf2i")
                                    .map(|v| v.into())
                                    .unwrap_or(val)
                            }
                            _ => val,
                        };
                        let _ = builder.build_store(alloca, i64_val);
                    }
                }
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
                } else {
                    // Source vreg undefined — insert default i64(0) to prevent cascade failures
                    let default_val = self.context.i64_type().const_int(0, false);
                    vreg_map.insert(*dest, default_val.into());
                }
            }
            MirInst::BinOp { dest, op, left, right } => {
                let left_val = self.get_vreg(left, vreg_map)?;
                let right_val = self.get_vreg(right, vreg_map)?;
                let result = self.compile_binop(*op, left_val, right_val, builder, module)?;
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
                if let Some(alloca) = local_allocas.get(local_index) {
                    vreg_map.insert(*dest, (*alloca).into());
                } else {
                    // Unknown local index — create a temporary alloca as fallback
                    let i64_type = self.context.i64_type();
                    let alloca = builder
                        .build_alloca(i64_type, &format!("local_{}", local_index))
                        .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;
                    vreg_map.insert(*dest, alloca.into());
                }
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
                self.compile_index_get(*dest, *collection, *index, vreg_map, builder, module)?;
            }
            MirInst::IndexSet {
                collection,
                index,
                value,
            } => {
                self.compile_index_set(*collection, *index, *value, vreg_map, builder, module)?;
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
                body_block: _,
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

            // =====================================================================
            // Unsupported instruction categories
            // =====================================================================

            // SIMD instructions (not yet implemented — insert default dest values)
            MirInst::VecLit { dest, .. }
            | MirInst::VecSum { dest, .. }
            | MirInst::VecProduct { dest, .. }
            | MirInst::VecMin { dest, .. }
            | MirInst::VecMax { dest, .. }
            | MirInst::VecAll { dest, .. }
            | MirInst::VecAny { dest, .. }
            | MirInst::VecExtract { dest, .. }
            | MirInst::VecWith { dest, .. }
            | MirInst::VecSqrt { dest, .. }
            | MirInst::VecAbs { dest, .. }
            | MirInst::VecFloor { dest, .. }
            | MirInst::VecCeil { dest, .. }
            | MirInst::VecRound { dest, .. }
            | MirInst::VecShuffle { dest, .. }
            | MirInst::VecBlend { dest, .. }
            | MirInst::VecSelect { dest, .. }
            | MirInst::VecLoad { dest, .. }
            | MirInst::VecGather { dest, .. }
            | MirInst::VecFma { dest, .. }
            | MirInst::VecRecip { dest, .. }
            | MirInst::VecMaskedLoad { dest, .. }
            | MirInst::VecMinVec { dest, .. }
            | MirInst::VecMaxVec { dest, .. }
            | MirInst::VecClamp { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            // SIMD store instructions (no dest vreg)
            MirInst::VecStore { .. }
            | MirInst::VecScatter { .. }
            | MirInst::VecMaskedStore { .. } => {
            }

            // Pointer instructions (not yet implemented — insert default dest values)
            MirInst::PointerNew { dest, .. }
            | MirInst::PointerRef { dest, .. }
            | MirInst::PointerDeref { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Memory safety instructions (not yet implemented)
            MirInst::Drop { .. } | MirInst::EndScope { .. } => {
                // Drop and scope tracking not yet implemented
            }

            // Pattern matching instructions (not yet implemented — insert default dest values)
            MirInst::PatternTest { dest, .. }
            | MirInst::PatternBind { dest, .. }
            | MirInst::EnumDiscriminant { dest, .. }
            | MirInst::EnumPayload { dest, .. }
            | MirInst::EnumUnit { dest, .. }
            | MirInst::EnumWith { dest, .. }
            | MirInst::UnionDiscriminant { dest, .. }
            | MirInst::UnionPayload { dest, .. }
            | MirInst::UnionWrap { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Async/Actor instructions (interpreter-only — insert default dest values)
            MirInst::FutureCreate { dest, .. }
            | MirInst::Await { dest, .. }
            | MirInst::ActorSpawn { dest, .. }
            | MirInst::ActorRecv { dest, .. }
            | MirInst::ActorJoin { dest, .. }
            | MirInst::GeneratorCreate { dest, .. }
            | MirInst::GeneratorNext { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            // Async instructions without dest vreg
            MirInst::ActorSend { .. }
            | MirInst::ActorReply { .. }
            | MirInst::Yield { .. } => {
            }

            // Error handling instructions
            MirInst::OptionSome { dest, value } => {
                // Option::Some(v) = v (in tagged runtime, non-nil is Some)
                let val = self.get_vreg(value, vreg_map)?;
                vreg_map.insert(*dest, val);
            }
            MirInst::OptionNone { dest } => {
                // Option::None = 0 (nil)
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::ResultOk { dest, value } => {
                // Result::Ok(v) = v (in tagged runtime)
                let val = self.get_vreg(value, vreg_map)?;
                vreg_map.insert(*dest, val);
            }
            MirInst::ResultErr { dest, value } => {
                // Result::Err(v) = v (in tagged runtime, error handling via runtime)
                let val = self.get_vreg(value, vreg_map)?;
                vreg_map.insert(*dest, val);
            }
            MirInst::TryUnwrap { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Contract instructions (not yet implemented)
            MirInst::ContractCheck { .. } => {
            }
            MirInst::ContractOldCapture { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Coverage instrumentation (not yet implemented)
            MirInst::DecisionProbe { .. } | MirInst::ConditionProbe { .. } | MirInst::PathProbe { .. } => {
                // Coverage instrumentation not yet implemented
            }

            // Unit type instructions (not yet implemented)
            MirInst::UnitBoundCheck { .. } => {
            }
            MirInst::UnitWiden { dest, .. }
            | MirInst::UnitNarrow { dest, .. }
            | MirInst::UnitSaturate { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Parallel iterator instructions (not yet implemented)
            MirInst::ParMap { dest, .. }
            | MirInst::ParReduce { dest, .. }
            | MirInst::ParFilter { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::ParForEach { .. } => {
            }

            // Boxing instructions — tag/untag values per RuntimeValue encoding
            // TAG_INT = 0b000, from_int(i) = i << 3, as_int() = val >> 3
            MirInst::BoxInt { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.context.i64_type();
                let int_val = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                    .into_int_value();
                let shifted = builder
                    .build_left_shift(int_val, i64_type.const_int(3, false), "box_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("box_int shift", &e))?;
                vreg_map.insert(*dest, shifted.into());
            }
            MirInst::UnboxInt { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.context.i64_type();
                let int_val = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                    .into_int_value();
                let shifted = builder
                    .build_right_shift(int_val, i64_type.const_int(3, false), true, "unbox_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox_int shift", &e))?;
                vreg_map.insert(*dest, shifted.into());
            }
            MirInst::BoxFloat { dest, value } => {
                // Box float: (bits >> 3) << 3 | TAG_FLOAT(2)
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.context.i64_type();
                let three = i64_type.const_int(3, false);
                let tag_float = i64_type.const_int(2, false);
                // Convert float to bits (i64)
                let bits = if val.is_float_value() {
                    builder.build_bit_cast(val.into_float_value(), i64_type, "f2i")
                        .map_err(|e| crate::error::factory::llvm_build_failed("bitcast", &e))?
                        .into_int_value()
                } else {
                    self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                        .into_int_value()
                };
                let shifted = builder.build_right_shift(bits, three, false, "ushr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("ushr", &e))?;
                let payload = builder.build_left_shift(shifted, three, "shl")
                    .map_err(|e| crate::error::factory::llvm_build_failed("shl", &e))?;
                let boxed = builder.build_or(payload, tag_float, "box_float")
                    .map_err(|e| crate::error::factory::llvm_build_failed("or", &e))?;
                vreg_map.insert(*dest, boxed.into());
            }
            MirInst::UnboxFloat { dest, value } => {
                // Unbox float: extract bits and shift back
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.context.i64_type();
                let f64_type = self.context.f64_type();
                let three = i64_type.const_int(3, false);
                let int_val = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                    .into_int_value();
                let shifted = builder.build_right_shift(int_val, three, false, "ushr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("ushr", &e))?;
                let bits = builder.build_left_shift(shifted, three, "shl")
                    .map_err(|e| crate::error::factory::llvm_build_failed("shl", &e))?;
                let unboxed = builder.build_bit_cast(bits, f64_type, "i2f")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bitcast", &e))?;
                vreg_map.insert(*dest, unboxed.into());
            }

            MirInst::Spread { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::FStringFormat { dest, parts } => {
                use crate::mir::FStringPart;
                let i64_type = self.context.i64_type();
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                // Declare runtime functions
                let string_new = module.get_function("rt_string_new").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[ptr_type.into(), i64_type.into()], false);
                    module.add_function("rt_string_new", fn_type, None)
                });
                let string_concat = module.get_function("rt_string_concat").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                    module.add_function("rt_string_concat", fn_type, None)
                });
                let value_to_string = module.get_function("rt_value_to_string").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function("rt_value_to_string", fn_type, None)
                });

                // Start with empty string
                let null_ptr = ptr_type.const_null();
                let zero = i64_type.const_int(0, false);
                let empty_call = builder
                    .build_call(string_new, &[null_ptr.into(), zero.into()], "empty_str")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
                let mut result = empty_call.try_as_basic_value().left()
                    .unwrap_or_else(|| i64_type.const_int(0, false).into());

                for part in parts {
                    let part_str = match part {
                        FStringPart::Literal(s) => {
                            if s.is_empty() { continue; }
                            let str_val = self.context.const_string(s.as_bytes(), false);
                            let global = module.add_global(str_val.get_type(), None, "fstr");
                            global.set_initializer(&str_val);
                            global.set_constant(true);
                            global.set_linkage(inkwell::module::Linkage::Private);
                            let str_ptr = global.as_pointer_value();
                            let str_len = i64_type.const_int(s.len() as u64, false);
                            let call = builder
                                .build_call(string_new, &[str_ptr.into(), str_len.into()], "lit_str")
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
                            call.try_as_basic_value().left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                        FStringPart::Expr(vreg) => {
                            let val = self.get_vreg(vreg, vreg_map)?;
                            let coerced = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                            let call = builder
                                .build_call(value_to_string, &[coerced.into()], "expr_str")
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_to_string", &e))?;
                            call.try_as_basic_value().left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                    };

                    let concat_call = builder
                        .build_call(string_concat, &[result.into(), part_str.into()], "concat")
                        .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_concat", &e))?;
                    result = concat_call.try_as_basic_value().left()
                        .unwrap_or_else(|| i64_type.const_int(0, false).into());
                }

                vreg_map.insert(*dest, result);
            }

            // MethodCallVirtual — vtable-based dispatch; in tagged-value ABI just call receiver as function pointer
            MirInst::MethodCallVirtual { dest, receiver, args, .. } => {
                let i64_type = self.context.i64_type();
                let mut all_args = vec![*receiver];
                all_args.extend_from_slice(args);
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in &all_args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                    arg_vals.push(casted.into());
                }
                // In tagged-value ABI, virtual calls are rare; just return default
                if let Some(d) = dest {
                    vreg_map.insert(*d, i64_type.const_int(0, false).into());
                }
            }
            // Method call instructions — compiled as regular function calls
            MirInst::MethodCallStatic { dest, receiver, func_name, args } => {
                let i64_type = self.context.i64_type();

                // Extract plain method name from qualified name (e.g., "text.len" -> "len")
                let method = func_name.rsplit('.').next().unwrap_or(func_name);

                // Map well-known methods to runtime functions
                let runtime_func = match method {
                    // Collection methods
                    "len" => Some("rt_len"),
                    "push" => Some("rt_array_push"),
                    "pop" => Some("rt_array_pop"),
                    "clear" => Some("rt_array_clear"),
                    "reverse" => Some("rt_array_reverse"),
                    "sort" => Some("rt_array_sort"),
                    "first" => Some("rt_array_first"),
                    "last" => Some("rt_array_last"),
                    "find" => Some("rt_array_find"),
                    "any" => Some("rt_array_any"),
                    "all" => Some("rt_array_all"),
                    "filter" => Some("rt_array_filter"),
                    "map" => Some("rt_option_map"),
                    // String methods
                    "starts_with" => Some("rt_string_starts_with"),
                    "ends_with" => Some("rt_string_ends_with"),
                    "concat" => Some("rt_string_concat"),
                    "contains" => Some("rt_contains"),
                    "char_at" | "at" => Some("rt_string_char_at"),
                    "join" => Some("rt_string_join"),
                    "trim" => Some("rt_string_trim"),
                    "split" => Some("rt_string_split"),
                    "replace" => Some("rt_string_replace"),
                    "to_upper" | "upper" => Some("rt_string_to_upper"),
                    "to_lower" | "lower" => Some("rt_string_to_lower"),
                    "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
                    "to_string" | "str" => Some("rt_to_string"),
                    // Index methods
                    "get" => Some("rt_index_get"),
                    "slice" | "substring" => Some("rt_slice"),
                    // Dict methods
                    "keys" => Some("rt_dict_keys"),
                    "values" => Some("rt_dict_values"),
                    "contains_key" | "has_key" => Some("rt_contains"),
                    // Option/Result methods
                    "unwrap" | "unwrap_or" => Some("rt_enum_payload"),
                    "is_none" => Some("rt_is_none"),
                    "is_some" => Some("rt_is_some"),
                    "is_ok" | "is_err" => Some("rt_enum_check_discriminant"),
                    _ => None,
                };

                if let Some(rt_name) = runtime_func {
                    // Call the runtime function with receiver + args
                    let mut all_args_vregs = vec![*receiver];
                    all_args_vregs.extend_from_slice(args);
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    for arg in &all_args_vregs {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                        arg_vals.push(casted.into());
                    }
                    let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                        all_args_vregs.iter().map(|_| i64_type.into()).collect();
                    let fn_type = i64_type.fn_type(&param_types, false);
                    let rt_func = module.get_function(rt_name).unwrap_or_else(|| {
                        module.add_function(rt_name, fn_type, None)
                    });
                    let declared_params = rt_func.get_type().get_param_types().len();
                    let call_site = if declared_params != all_args_vregs.len() {
                        let fn_ptr = rt_func.as_global_value().as_pointer_value();
                        builder.build_indirect_call(fn_type, fn_ptr, &arg_vals, "rtcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt method call", &e))?
                    } else {
                        builder.build_call(rt_func, &arg_vals, "rtcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt method call", &e))?
                    };
                    // For in-place mutating methods, return receiver
                    let in_place = matches!(method, "push" | "clear" | "reverse" | "sort");
                    if let Some(d) = dest {
                        if in_place {
                            let recv_val = self.get_vreg(receiver, vreg_map)?;
                            vreg_map.insert(*d, recv_val);
                        } else if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                } else {
                    // Fall back: look up function by exact name or suffix match
                    let mut all_args = vec![*receiver];
                    all_args.extend_from_slice(args);
                    let called_func = module.get_function(func_name).or_else(|| {
                        let suffix = format!(".{}", func_name);
                        let mut func_opt = module.get_first_function();
                        let mut best: Option<inkwell::values::FunctionValue> = None;
                        while let Some(f) = func_opt {
                            let name = f.get_name().to_string_lossy().to_string();
                            if name.ends_with(&suffix) {
                                if best.as_ref().map_or(true, |b| name.len() < b.get_name().to_bytes().len()) {
                                    best = Some(f);
                                }
                            }
                            func_opt = f.get_next_function();
                        }
                        best
                    });

                    if let Some(func) = called_func {
                        let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                        for arg in &all_args {
                            let val = self.get_vreg(arg, vreg_map)?;
                            let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                            arg_vals.push(casted.into());
                        }
                        let declared_params = func.get_type().get_param_types().len();
                        let call_site = if declared_params != all_args.len() {
                            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                                all_args.iter().map(|_| i64_type.into()).collect();
                            let fn_type = i64_type.fn_type(&param_types, false);
                            let fn_ptr = func.as_global_value().as_pointer_value();
                            builder.build_indirect_call(fn_type, fn_ptr, &arg_vals, "mcall")
                                .map_err(|e| crate::error::factory::llvm_build_failed("method call", &e))?
                        } else {
                            builder.build_call(func, &arg_vals, "mcall")
                                .map_err(|e| crate::error::factory::llvm_build_failed("method call", &e))?
                        };
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            } else {
                                vreg_map.insert(*d, i64_type.const_int(0, false).into());
                            }
                        }
                    } else {
                        if let Some(d) = dest {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                }
            }
            MirInst::BuiltinMethod { dest, receiver, method, args, .. } => {
                // Compile as a regular function call with the method name
                let i64_type = self.context.i64_type();
                let mut all_args = vec![*receiver];
                all_args.extend_from_slice(args);
                let func = module.get_function(method);
                if let Some(func) = func {
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    for arg in &all_args {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                        arg_vals.push(casted.into());
                    }
                    let declared_params = func.get_type().get_param_types().len();
                    let call_site = if declared_params != all_args.len() {
                        let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                            all_args.iter().map(|_| i64_type.into()).collect();
                        let fn_type = i64_type.fn_type(&param_types, false);
                        let fn_ptr = func.as_global_value().as_pointer_value();
                        builder.build_indirect_call(fn_type, fn_ptr, &arg_vals, "bcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("builtin call", &e))?
                    } else {
                        builder.build_call(func, &arg_vals, "bcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("builtin call", &e))?
                    };
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                } else {
                    if let Some(d) = dest {
                        vreg_map.insert(*d, i64_type.const_int(0, false).into());
                    }
                }
            }
            MirInst::ExternMethodCall { dest, receiver, class_name, method_name, args, .. } => {
                // Compile as ClassName.method_name(receiver?, args...)
                let i64_type = self.context.i64_type();
                let full_name = format!("{}.{}", class_name, method_name);
                let mut all_args: Vec<crate::mir::VReg> = Vec::new();
                if let Some(r) = receiver {
                    all_args.push(*r);
                }
                all_args.extend_from_slice(args);
                let func = module.get_function(&full_name)
                    .or_else(|| module.get_function(method_name));
                if let Some(func) = func {
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    for arg in &all_args {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                        arg_vals.push(casted.into());
                    }
                    let declared_params = func.get_type().get_param_types().len();
                    let call_site = if declared_params != all_args.len() {
                        let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                            all_args.iter().map(|_| i64_type.into()).collect();
                        let fn_type = i64_type.fn_type(&param_types, false);
                        let fn_ptr = func.as_global_value().as_pointer_value();
                        builder.build_indirect_call(fn_type, fn_ptr, &arg_vals, "ecall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("extern call", &e))?
                    } else {
                        builder.build_call(func, &arg_vals, "ecall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("extern call", &e))?
                    };
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                } else {
                    if let Some(d) = dest {
                        vreg_map.insert(*d, i64_type.const_int(0, false).into());
                    }
                }
            }

            // Global variable access
            MirInst::GlobalLoad { dest, global_name, ty } => {
                let i64_type = self.context.i64_type();
                // Look up global variable, or create one
                let global = module.get_global(global_name).unwrap_or_else(|| {
                    let g = module.add_global(i64_type, None, global_name);
                    g.set_initializer(&i64_type.const_int(0, false));
                    g.set_linkage(inkwell::module::Linkage::WeakAny);
                    g
                });
                let loaded = builder
                    .build_load(i64_type, global.as_pointer_value(), "gload")
                    .map_err(|e| crate::error::factory::llvm_build_failed("global load", &e))?;
                vreg_map.insert(*dest, loaded);
            }
            MirInst::GlobalStore { global_name, value, ty } => {
                let i64_type = self.context.i64_type();
                let val = self.get_vreg(value, vreg_map)?;
                let coerced = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                let global = module.get_global(global_name).unwrap_or_else(|| {
                    let g = module.add_global(i64_type, None, global_name);
                    g.set_initializer(&i64_type.const_int(0, false));
                    g.set_linkage(inkwell::module::Linkage::WeakAny);
                    g
                });
                let _ = builder.build_store(global.as_pointer_value(), coerced);
            }
            // Advanced memory instructions (not yet implemented — insert default dest values)
            MirInst::GetElementPtr { dest, .. }
            | MirInst::NeighborLoad { dest, .. } => {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::Wait { dest, .. } => {
                if let Some(d) = dest {
                    let default_val = self.context.i64_type().const_int(0, false);
                    vreg_map.insert(*d, default_val.into());
                }
            }
            MirInst::GlobalStore { .. } => {
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
        Ok(vreg_map
            .get(vreg)
            .copied()
            .unwrap_or_else(|| self.context.i64_type().const_int(0, false).into()))
    }
}

// ============================================================================
// Stub implementation for non-LLVM builds
// ============================================================================

#[cfg(not(feature = "llvm"))]
impl LlvmBackend {
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }
}
