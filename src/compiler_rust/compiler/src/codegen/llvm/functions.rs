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
#[cfg(feature = "llvm")]
use inkwell::InlineAsmDialect;

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
    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn build_box_float_value(
        &self,
        val: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::IntValue<'static>, CompileError> {
        let rv_type = self.runtime_int_type();
        let rv_width = rv_type.get_bit_width();

        if rv_width == 64 {
            let bits = if val.is_float_value() {
                builder
                    .build_bit_cast(val.into_float_value(), rv_type, "f2i")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bitcast", &e))?
                    .into_int_value()
            } else {
                self.coerce_value_to_type(val, Some(rv_type.into()), builder)?
                    .into_int_value()
            };
            let three = rv_type.const_int(3, false);
            let tag_float = rv_type.const_int(2, false);
            let shifted = builder
                .build_right_shift(bits, three, false, "ushr")
                .map_err(|e| crate::error::factory::llvm_build_failed("ushr", &e))?;
            let payload = builder
                .build_left_shift(shifted, three, "shl")
                .map_err(|e| crate::error::factory::llvm_build_failed("shl", &e))?;
            return builder
                .build_or(payload, tag_float, "box_float")
                .map_err(|e| crate::error::factory::llvm_build_failed("or", &e));
        }

        let f64_type = self.context.f64_type();
        let f64_val = match val {
            inkwell::values::BasicValueEnum::FloatValue(fv) if fv.get_type() == f64_type => fv,
            inkwell::values::BasicValueEnum::FloatValue(fv) => builder
                .build_float_ext(fv, f64_type, "box_fext")
                .map_err(|e| crate::error::factory::llvm_build_failed("float_ext", &e))?,
            inkwell::values::BasicValueEnum::IntValue(iv) => builder
                .build_signed_int_to_float(iv, f64_type, "box_sitofp")
                .map_err(|e| crate::error::factory::llvm_build_failed("int_to_float", &e))?,
            inkwell::values::BasicValueEnum::PointerValue(pv) => {
                let iv = builder
                    .build_ptr_to_int(pv, rv_type, "box_ptrtoint")
                    .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
                builder
                    .build_signed_int_to_float(iv, f64_type, "box_ptr_sitofp")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_float", &e))?
            }
            _ => f64_type.const_zero(),
        };

        let fn_type = rv_type.fn_type(&[f64_type.into()], false);
        let func = module
            .get_function("rt_box_float")
            .unwrap_or_else(|| module.add_function("rt_box_float", fn_type, None));
        let call = builder
            .build_call(func, &[f64_val.into()], "rt_box_float")
            .map_err(|e| crate::error::factory::llvm_build_failed("call rt_box_float", &e))?;
        let ret = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::semantic("rt_box_float returned no value".to_string()))?
            .into_int_value();
        Ok(ret)
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn build_unbox_float_value(
        &self,
        val: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::FloatValue<'static>, CompileError> {
        let rv_type = self.runtime_int_type();
        let f64_type = self.context.f64_type();

        let int_val = self
            .coerce_value_to_type(val, Some(rv_type.into()), builder)?
            .into_int_value();
        if rv_type.get_bit_width() == 64 {
            let three = rv_type.const_int(3, false);
            let shifted = builder
                .build_right_shift(int_val, three, false, "ushr")
                .map_err(|e| crate::error::factory::llvm_build_failed("ushr", &e))?;
            let bits = builder
                .build_left_shift(shifted, three, "shl")
                .map_err(|e| crate::error::factory::llvm_build_failed("shl", &e))?;
            return Ok(builder
                .build_bit_cast(bits, f64_type, "i2f")
                .map_err(|e| crate::error::factory::llvm_build_failed("bitcast", &e))?
                .into_float_value());
        }

        let fn_type = f64_type.fn_type(&[rv_type.into()], false);
        let func = module
            .get_function("rt_unbox_float")
            .unwrap_or_else(|| module.add_function("rt_unbox_float", fn_type, None));
        let call = builder
            .build_call(func, &[int_val.into()], "rt_unbox_float")
            .map_err(|e| crate::error::factory::llvm_build_failed("call rt_unbox_float", &e))?;
        Ok(call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::semantic("rt_unbox_float returned no value".to_string()))?
            .into_float_value())
    }

    /// Compile a MIR function to LLVM IR (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_function(&self, func: &MirFunction) -> Result<(), CompileError> {
        use crate::hir::TypeId;
        use std::collections::HashMap;
        use std::collections::HashSet;

        let dump_filter = std::env::var("SIMPLE_DUMP_IR_FILTER").ok();
        let should_dump = std::env::var("SIMPLE_DUMP_IR").is_ok()
            && dump_filter
                .as_deref()
                .map(|needle| func.name.contains(needle))
                .unwrap_or_else(|| func.name.contains("native_build"));

        // Debug: dump MIR for selected functions when SIMPLE_DUMP_IR is set.
        if should_dump {
            eprintln!("=== MIR for {} ===", func.name);
            eprintln!(
                "  params: {:?}",
                func.params.iter().map(|p| (&p.name, &p.ty)).collect::<Vec<_>>()
            );
            eprintln!(
                "  locals: {:?}",
                func.locals.iter().map(|l| (&l.name, &l.ty)).collect::<Vec<_>>()
            );
            for block in &func.blocks {
                eprintln!("  block {}:", block.id.0);
                for inst in &block.instructions {
                    eprintln!("    {:?}", inst);
                }
                eprintln!("    terminator: {:?}", block.terminator);
            }
            eprintln!("=== END MIR ===");
        }

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_builder_not_created)?;

        // Resolve through import_map/use_map to get the mangled name
        let resolved_name = self
            .use_map
            .get(&func.name)
            .or_else(|| self.import_map.get(&func.name))
            .map(|s| s.as_str())
            .unwrap_or(&func.name);

        // Get the function that was forward-declared in the compile() pass
        // If it doesn't exist, create it (for backwards compatibility)
        let function = module.get_function(resolved_name).unwrap_or_else(|| {
            let i64_type = self.runtime_int_type();
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                func.params.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(resolved_name, fn_type, None)
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
                crate::mir::Terminator::Return(Some(v)) => {
                    all_vregs.insert(*v);
                }
                crate::mir::Terminator::Branch { cond, .. } => {
                    all_vregs.insert(*cond);
                }
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
            let i64_type = self.runtime_int_type();
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

            // Rebuild the visible SSA state from allocas at every block boundary.
            // Leaving stale non-live values from a previous block in vreg_map can
            // feed the wrong receiver/operand into later calls.
            vreg_map.clear();

            // At the start of each block, reload the vregs that are live-in to
            // that block. For the entry block, seed parameter vregs.
            if Some(block.id) == is_entry_block_id {
                let i64_type = self.runtime_int_type();
                for (i, _param) in func.params.iter().enumerate() {
                    let vreg = crate::mir::VReg(i as u32);
                    if let Some(&alloca) = vreg_allocas.get(&vreg) {
                        if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", vreg.0)) {
                            vreg_map.insert(vreg, val);
                        }
                    }
                }
            } else {
                vreg_map.clear();

                // Compute vregs used before their first local definition.
                let mut seen_defs = HashSet::new();
                let mut live_in = HashSet::new();
                for inst in &block.instructions {
                    for u in inst.uses() {
                        if !seen_defs.contains(&u) {
                            live_in.insert(u);
                        }
                    }
                    if let Some(d) = inst.dest() {
                        seen_defs.insert(d);
                    }
                }
                match &block.terminator {
                    crate::mir::Terminator::Return(Some(v)) => {
                        if !seen_defs.contains(v) {
                            live_in.insert(*v);
                        }
                    }
                    crate::mir::Terminator::Branch { cond, .. } => {
                        if !seen_defs.contains(cond) {
                            live_in.insert(*cond);
                        }
                    }
                    _ => {}
                }

                // Load only live-in vregs from allocas
                let i64_type = self.runtime_int_type();
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
                let i64_type = self.runtime_int_type();
                for used in inst.uses() {
                    if vreg_map.contains_key(&used) {
                        continue;
                    }
                    if let Some(&alloca) = vreg_allocas.get(&used) {
                        if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", used.0)) {
                            vreg_map.insert(used, val);
                        }
                    }
                }

                self.compile_instruction(inst, &mut vreg_map, &local_allocas, builder, module)?;

                // Store any newly defined vreg to its alloca (for cross-block access)
                if let Some(d) = inst.dest() {
                    if let (Some(&alloca), Some(&val)) = (vreg_allocas.get(&d), vreg_map.get(&d)) {
                        // Coerce value to RuntimeValue int width before storing
                        let rv_type = self.runtime_int_type();
                        let rv_width = rv_type.get_bit_width();
                        let i64_val = match val {
                            inkwell::values::BasicValueEnum::IntValue(iv) => {
                                let bw = iv.get_type().get_bit_width();
                                if bw == rv_width {
                                    val
                                } else if bw < rv_width {
                                    builder
                                        .build_int_z_extend(iv, rv_type, "vext")
                                        .map(|v| v.into())
                                        .unwrap_or(val)
                                } else {
                                    builder
                                        .build_int_truncate(iv, rv_type, "vtrunc")
                                        .map(|v| v.into())
                                        .unwrap_or(val)
                                }
                            }
                            inkwell::values::BasicValueEnum::PointerValue(pv) => builder
                                .build_ptr_to_int(pv, rv_type, "vp2i")
                                .map(|v| v.into())
                                .unwrap_or(val),
                            inkwell::values::BasicValueEnum::FloatValue(fv) => builder
                                .build_float_to_signed_int(fv, rv_type, "vf2i")
                                .map(|v| v.into())
                                .unwrap_or(val),
                            _ => val,
                        };
                        let _ = builder.build_store(alloca, i64_val);
                    }
                }

                vreg_map.clear();
            }

            // Compile terminator
            let i64_type = self.runtime_int_type();
            match &block.terminator {
                crate::mir::Terminator::Return(Some(v)) => {
                    if !vreg_map.contains_key(v) {
                        if let Some(&alloca) = vreg_allocas.get(v) {
                            if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", v.0)) {
                                vreg_map.insert(*v, val);
                            }
                        }
                    }
                }
                crate::mir::Terminator::Branch { cond, .. } => {
                    if !vreg_map.contains_key(cond) {
                        if let Some(&alloca) = vreg_allocas.get(cond) {
                            if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", cond.0)) {
                                vreg_map.insert(*cond, val);
                            }
                        }
                    }
                }
                _ => {}
            }
            self.compile_terminator(&block.terminator, &llvm_blocks, &vreg_map, builder)?;
        }

        // Debug: dump LLVM IR to file for selected functions.
        if should_dump {
            let ir_path = format!(
                "/tmp/llvm_ir_{}.ll",
                func.name.replace(|c: char| !c.is_alphanumeric(), "_")
            );
            if let Err(e) = module.print_to_file(&ir_path) {
                eprintln!("Warning: could not dump LLVM IR to {}: {}", ir_path, e);
            } else {
                eprintln!("Dumped LLVM IR for {} to {}", func.name, ir_path);
            }
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
                    let default_val = self.runtime_int_type().const_int(0, false);
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
                    let i64_type = self.runtime_int_type();
                    let alloca = builder
                        .build_alloca(i64_type, &format!("local_{}", local_index))
                        .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;
                    vreg_map.insert(*dest, alloca.into());
                }
            }

            // Collections
            MirInst::ArrayLit { dest, elements } => {
                self.compile_array_lit(*dest, elements, vreg_map, builder, module)?;
            }
            MirInst::TupleLit { dest, elements } => {
                self.compile_tuple_lit(*dest, elements, vreg_map, builder, module)?;
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
            MirInst::InlineAsm { instructions, .. } => {
                if !matches!(
                    self.target.arch,
                    simple_common::target::TargetArch::X86 | simple_common::target::TargetArch::X86_64
                ) {
                    // Inline asm blocks are target-specific. Full-tree OS builds can still
                    // compile unrelated x86 modules while targeting RISC-V.
                } else {
                    let fn_type = self.context.void_type().fn_type(&[], false);
                    let asm = self.context.create_inline_asm(
                        fn_type,
                        instructions.join("\n"),
                        String::new(),
                        true,
                        false,
                        Some(InlineAsmDialect::ATT),
                        false,
                    );
                    builder
                        .build_indirect_call(fn_type, asm, &[], "")
                        .map_err(|e| crate::error::factory::llvm_build_failed("inline_asm", &e))?;
                }
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

            // GPU memory load/store (not used in LLVM AOT path — stub)
            MirInst::GpuLoadF64 { dest, .. } | MirInst::GpuLoadI64 { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::GpuStoreF64 { .. } | MirInst::GpuStoreI64 { .. } => {}

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
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            // SIMD store instructions (no dest vreg)
            MirInst::VecStore { .. } | MirInst::VecScatter { .. } | MirInst::VecMaskedStore { .. } => {}

            // Pointer instructions (not yet implemented — insert default dest values)
            MirInst::PointerNew { dest, .. }
            | MirInst::PointerRef { dest, .. }
            | MirInst::PointerDeref { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Memory safety instructions (not yet implemented)
            MirInst::Drop { .. } | MirInst::EndScope { .. } => {
                // Drop and scope tracking not yet implemented
            }

            // Pattern matching
            MirInst::PatternTest { dest, subject, pattern } => {
                let i64_type = self.runtime_int_type();
                let subject_val = self.get_vreg_val(subject, vreg_map, i64_type);
                let result = match pattern {
                    crate::mir::MirPattern::Wildcard | crate::mir::MirPattern::Binding(_) => {
                        i64_type.const_int(1, false)
                    }
                    crate::mir::MirPattern::Literal(lit) => match lit {
                        crate::mir::MirLiteral::Int(n) => {
                            let lit_val = i64_type.const_int(*n as u64, false);
                            let cmp = builder
                                .build_int_compare(
                                    inkwell::IntPredicate::EQ,
                                    subject_val.into_int_value(),
                                    lit_val,
                                    "pat_int_eq",
                                )
                                .map_err(|e| format!("pattern icmp: {e}"))?;
                            builder
                                .build_int_z_extend(cmp, i64_type, "pat_ext")
                                .map_err(|e| format!("pattern zext: {e}"))?
                        }
                        crate::mir::MirLiteral::Bool(b) => {
                            let lit_val = i64_type.const_int(if *b { 1 } else { 0 }, false);
                            let cmp = builder
                                .build_int_compare(
                                    inkwell::IntPredicate::EQ,
                                    subject_val.into_int_value(),
                                    lit_val,
                                    "pat_bool_eq",
                                )
                                .map_err(|e| format!("pattern icmp: {e}"))?;
                            builder
                                .build_int_z_extend(cmp, i64_type, "pat_ext")
                                .map_err(|e| format!("pattern zext: {e}"))?
                        }
                        crate::mir::MirLiteral::Nil => {
                            let nil_val = i64_type.const_int(3, false); // TAG_SPECIAL | NIL
                            let cmp = builder
                                .build_int_compare(
                                    inkwell::IntPredicate::EQ,
                                    subject_val.into_int_value(),
                                    nil_val,
                                    "pat_nil_eq",
                                )
                                .map_err(|e| format!("pattern icmp: {e}"))?;
                            builder
                                .build_int_z_extend(cmp, i64_type, "pat_ext")
                                .map_err(|e| format!("pattern zext: {e}"))?
                        }
                        crate::mir::MirLiteral::String(s) => {
                            // Create string constant and compare with rt_string_eq
                            let bytes = s.as_bytes();
                            let global_val = self.context.const_string(bytes, false);
                            let global = module.add_global(global_val.get_type(), None, "pat_str_const");
                            global.set_initializer(&global_val);
                            global.set_constant(true);
                            let str_ptr = builder
                                .build_pointer_cast(
                                    global.as_pointer_value(),
                                    self.context.ptr_type(inkwell::AddressSpace::default()),
                                    "str_ptr",
                                )
                                .map_err(|e| format!("pattern str ptr: {e}"))?;
                            let str_ptr_int = builder
                                .build_ptr_to_int(str_ptr, i64_type, "str_ptr_int")
                                .map_err(|e| format!("pattern ptrtoint: {e}"))?;
                            let str_len = i64_type.const_int(bytes.len() as u64, false);
                            // rt_string_new(ptr, len) -> RuntimeValue
                            let rt_string_new = module.get_function("rt_string_new").unwrap_or_else(|| {
                                let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                                module.add_function("rt_string_new", fn_type, None)
                            });
                            let lit_str = builder
                                .build_call(rt_string_new, &[str_ptr_int.into(), str_len.into()], "lit_str")
                                .map_err(|e| format!("pattern string_new: {e}"))?
                                .try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into());
                            // rt_string_eq(a, b) -> i64
                            let rt_string_eq = module.get_function("rt_string_eq").unwrap_or_else(|| {
                                let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                                module.add_function("rt_string_eq", fn_type, None)
                            });
                            builder
                                .build_call(rt_string_eq, &[subject_val.into(), lit_str.into()], "pat_str_eq")
                                .map_err(|e| format!("pattern string_eq: {e}"))?
                                .try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                                .into_int_value()
                        }
                        crate::mir::MirLiteral::Float(f) => {
                            let lit_bits = f.to_bits() as u64;
                            let lit_val = i64_type.const_int(lit_bits, false);
                            let cmp = builder
                                .build_int_compare(
                                    inkwell::IntPredicate::EQ,
                                    subject_val.into_int_value(),
                                    lit_val,
                                    "pat_float_eq",
                                )
                                .map_err(|e| format!("pattern icmp: {e}"))?;
                            builder
                                .build_int_z_extend(cmp, i64_type, "pat_ext")
                                .map_err(|e| format!("pattern zext: {e}"))?
                        }
                    },
                    crate::mir::MirPattern::Variant { variant_name, .. } => {
                        // Get discriminant and compare
                        let rt_enum_disc = module.get_function("rt_enum_discriminant").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_enum_discriminant", fn_type, None)
                        });
                        let disc = builder
                            .build_call(rt_enum_disc, &[subject_val.into()], "disc")
                            .map_err(|e| format!("pattern disc: {e}"))?
                            .try_as_basic_value()
                            .left()
                            .unwrap_or_else(|| i64_type.const_int(0, false).into())
                            .into_int_value();
                        let expected = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::hash::{Hash, Hasher};
                            let mut hasher = DefaultHasher::new();
                            variant_name.hash(&mut hasher);
                            (hasher.finish() & 0xFFFFFFFF) as u64
                        };
                        let expected_val = i64_type.const_int(expected, false);
                        let cmp = builder
                            .build_int_compare(inkwell::IntPredicate::EQ, disc, expected_val, "pat_var_eq")
                            .map_err(|e| format!("pattern var icmp: {e}"))?;
                        builder
                            .build_int_z_extend(cmp, i64_type, "pat_ext")
                            .map_err(|e| format!("pattern zext: {e}"))?
                    }
                    _ => {
                        // Struct/tuple/other: always match (destructuring handled by PatternBind)
                        i64_type.const_int(1, false)
                    }
                };
                vreg_map.insert(*dest, result.into());
            }

            MirInst::PatternBind { dest, subject, binding } => {
                let i64_type = self.runtime_int_type();
                let subject_val = self.get_vreg_val(subject, vreg_map, i64_type);
                let result = if binding.path.is_empty() {
                    subject_val
                } else {
                    // Apply binding path steps
                    let mut current = subject_val;
                    for step in &binding.path {
                        match step {
                            crate::mir::BindingStep::EnumPayload => {
                                let rt_enum_payload = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                                    module.add_function("rt_enum_payload", fn_type, None)
                                });
                                current = builder
                                    .build_call(rt_enum_payload, &[current.into()], "payload")
                                    .map_err(|e| format!("pattern bind payload: {e}"))?
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap_or_else(|| i64_type.const_int(0, false).into());
                            }
                            crate::mir::BindingStep::TupleIndex(idx) => {
                                let rt_tuple_get = module.get_function("rt_tuple_get").unwrap_or_else(|| {
                                    let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                                    module.add_function("rt_tuple_get", fn_type, None)
                                });
                                let idx_val = i64_type.const_int(*idx as u64, false);
                                current = builder
                                    .build_call(rt_tuple_get, &[current.into(), idx_val.into()], "tuple_el")
                                    .map_err(|e| format!("pattern bind tuple: {e}"))?
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap_or_else(|| i64_type.const_int(0, false).into());
                            }
                            crate::mir::BindingStep::FieldName(_) => {
                                // Field access on struct — subject is already a pointer
                                // For now, pass through (field offset not available in FieldName)
                            }
                        }
                    }
                    current
                };
                vreg_map.insert(*dest, result);
            }

            // Enum instructions
            MirInst::EnumDiscriminant { dest, value } => {
                let i64_t = self.runtime_int_type();
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                let rt_fn = module.get_function("rt_enum_discriminant").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i64_t.into()], false);
                    module.add_function("rt_enum_discriminant", fn_type, None)
                });
                let result = builder
                    .build_call(rt_fn, &[val.into()], "disc")
                    .map_err(|e| CompileError::Semantic(format!("enum disc call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::EnumPayload { dest, value } => {
                let i64_t = self.runtime_int_type();
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                let rt_fn = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i64_t.into()], false);
                    module.add_function("rt_enum_payload", fn_type, None)
                });
                let result = builder
                    .build_call(rt_fn, &[val.into()], "payload")
                    .map_err(|e| CompileError::Semantic(format!("enum payload call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::EnumUnit { dest, variant_name, .. } => {
                // rt_enum_new(enum_id: u32, discriminant: u32, payload: RuntimeValue) -> RuntimeValue
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    variant_name.hash(&mut hasher);
                    (hasher.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let enum_id_val = i32_t.const_int(0, false);
                let disc_val = i32_t.const_int(disc as u64, false);
                // NIL = 3 (TAG_SPECIAL=0b011 | SPECIAL_NIL=0)
                let nil_val = i64_t.const_int(3, false);
                let result = builder
                    .build_call(
                        rt_fn,
                        &[enum_id_val.into(), disc_val.into(), nil_val.into()],
                        "enum_unit",
                    )
                    .map_err(|e| CompileError::Semantic(format!("enum unit call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::EnumWith {
                dest,
                variant_name,
                payload,
                ..
            } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    variant_name.hash(&mut hasher);
                    (hasher.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let enum_id_val = i32_t.const_int(0, false);
                let disc_val = i32_t.const_int(disc as u64, false);
                let payload_val = vreg_map
                    .get(payload)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(3, false).into());
                let payload_val = self.coerce_value_to_type(payload_val, Some(i64_t.into()), builder)?;
                let result = builder
                    .build_call(
                        rt_fn,
                        &[enum_id_val.into(), disc_val.into(), payload_val.into()],
                        "enum_with",
                    )
                    .map_err(|e| CompileError::Semantic(format!("enum with call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            // Union instructions — use same enum runtime functions
            MirInst::UnionDiscriminant { dest, value } => {
                let i64_t = self.runtime_int_type();
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                let rt_fn = module.get_function("rt_enum_discriminant").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i64_t.into()], false);
                    module.add_function("rt_enum_discriminant", fn_type, None)
                });
                let result = builder
                    .build_call(rt_fn, &[val.into()], "union_disc")
                    .map_err(|e| CompileError::Semantic(format!("union disc call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::UnionPayload { dest, value, .. } => {
                let i64_t = self.runtime_int_type();
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                let rt_fn = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i64_t.into()], false);
                    module.add_function("rt_enum_payload", fn_type, None)
                });
                let result = builder
                    .build_call(rt_fn, &[val.into()], "union_payload")
                    .map_err(|e| CompileError::Semantic(format!("union payload call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::UnionWrap {
                dest,
                value,
                type_index,
            } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let enum_id_val = i32_t.const_int(*type_index as u64, false);
                let disc_val = i32_t.const_int(0, false);
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(3, false).into());
                let result = builder
                    .build_call(rt_fn, &[enum_id_val.into(), disc_val.into(), val.into()], "union_wrap")
                    .map_err(|e| CompileError::Semantic(format!("union wrap call: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }

            // Async/Actor instructions (interpreter-only — insert default dest values)
            MirInst::FutureCreate { dest, .. }
            | MirInst::Await { dest, .. }
            | MirInst::ActorSpawn { dest, .. }
            | MirInst::ActorRecv { dest, .. }
            | MirInst::ActorJoin { dest, .. }
            | MirInst::GeneratorCreate { dest, .. }
            | MirInst::GeneratorNext { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            // Async instructions without dest vreg
            MirInst::ActorSend { .. } | MirInst::ActorReply { .. } | MirInst::Yield { .. } => {}

            // Error handling instructions — use rt_enum_new for proper enum representation
            MirInst::OptionSome { dest, value } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut h = DefaultHasher::new();
                    "Some".hash(&mut h);
                    (h.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let val = self.get_vreg(value, vreg_map)?;
                let val = self.coerce_value_to_type(val, Some(i64_t.into()), builder)?;
                let result = builder
                    .build_call(
                        rt_fn,
                        &[
                            i32_t.const_int(1, false).into(),
                            i32_t.const_int(disc as u64, false).into(),
                            val.into(),
                        ],
                        "opt_some",
                    )
                    .map_err(|e| CompileError::Semantic(format!("option some: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::OptionNone { dest } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut h = DefaultHasher::new();
                    "None".hash(&mut h);
                    (h.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let nil_val = i64_t.const_int(3, false); // NIL = 3
                let result = builder
                    .build_call(
                        rt_fn,
                        &[
                            i32_t.const_int(1, false).into(),
                            i32_t.const_int(disc as u64, false).into(),
                            nil_val.into(),
                        ],
                        "opt_none",
                    )
                    .map_err(|e| CompileError::Semantic(format!("option none: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::ResultOk { dest, value } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut h = DefaultHasher::new();
                    "Ok".hash(&mut h);
                    (h.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let val = self.get_vreg(value, vreg_map)?;
                let val = self.coerce_value_to_type(val, Some(i64_t.into()), builder)?;
                let result = builder
                    .build_call(
                        rt_fn,
                        &[
                            i32_t.const_int(0, false).into(),
                            i32_t.const_int(disc as u64, false).into(),
                            val.into(),
                        ],
                        "res_ok",
                    )
                    .map_err(|e| CompileError::Semantic(format!("result ok: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::ResultErr { dest, value } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context.i32_type();
                let disc = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut h = DefaultHasher::new();
                    "Err".hash(&mut h);
                    (h.finish() & 0xFFFFFFFF) as u32
                };
                let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
                    module.add_function("rt_enum_new", fn_type, None)
                });
                let val = self.get_vreg(value, vreg_map)?;
                let val = self.coerce_value_to_type(val, Some(i64_t.into()), builder)?;
                let result = builder
                    .build_call(
                        rt_fn,
                        &[
                            i32_t.const_int(0, false).into(),
                            i32_t.const_int(disc as u64, false).into(),
                            val.into(),
                        ],
                        "res_err",
                    )
                    .map_err(|e| CompileError::Semantic(format!("result err: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }
            MirInst::TryUnwrap {
                dest,
                value,
                error_block: _,
                error_dest: _,
            } => {
                let i64_t = self.runtime_int_type();
                // Extract payload from Result/Option enum
                let val = vreg_map
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| i64_t.const_int(3, false).into());
                let rt_fn = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                    let fn_type = i64_t.fn_type(&[i64_t.into()], false);
                    module.add_function("rt_enum_payload", fn_type, None)
                });
                let result = builder
                    .build_call(rt_fn, &[val.into()], "try_unwrap")
                    .map_err(|e| CompileError::Semantic(format!("try unwrap: {e}")))?
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_t.const_int(0, false).into());
                vreg_map.insert(*dest, result);
            }

            // Contract instructions (not yet implemented)
            MirInst::ContractCheck { .. } => {}
            MirInst::ContractOldCapture { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Coverage instrumentation (not yet implemented)
            MirInst::DecisionProbe { .. } | MirInst::ConditionProbe { .. } | MirInst::PathProbe { .. } => {
                // Coverage instrumentation not yet implemented
            }

            // Unit type instructions (not yet implemented)
            MirInst::UnitBoundCheck { .. } => {}
            MirInst::UnitWiden { dest, .. } | MirInst::UnitNarrow { dest, .. } | MirInst::UnitSaturate { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }

            // Parallel iterator instructions (not yet implemented)
            MirInst::ParMap { dest, .. } | MirInst::ParReduce { dest, .. } | MirInst::ParFilter { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::ParForEach { .. } => {}

            // Boxing instructions — tag/untag values per RuntimeValue encoding
            // TAG_INT = 0b000, from_int(i) = i << 3, as_int() = val >> 3
            MirInst::BoxInt { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.runtime_int_type();
                let int_val = self
                    .coerce_value_to_type(val, Some(i64_type.into()), builder)?
                    .into_int_value();
                let shifted = builder
                    .build_left_shift(int_val, i64_type.const_int(3, false), "box_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("box_int shift", &e))?;
                vreg_map.insert(*dest, shifted.into());
            }
            MirInst::UnboxInt { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let i64_type = self.runtime_int_type();
                let int_val = self
                    .coerce_value_to_type(val, Some(i64_type.into()), builder)?
                    .into_int_value();
                let shifted = builder
                    .build_right_shift(int_val, i64_type.const_int(3, false), true, "unbox_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox_int shift", &e))?;
                vreg_map.insert(*dest, shifted.into());
            }
            MirInst::BoxFloat { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let boxed = self.build_box_float_value(val, builder, module)?;
                vreg_map.insert(*dest, boxed.into());
            }
            MirInst::UnboxFloat { dest, value } => {
                let val = self.get_vreg(value, vreg_map)?;
                let unboxed = self.build_unbox_float_value(val, builder, module)?;
                vreg_map.insert(*dest, unboxed.into());
            }

            MirInst::Spread { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::FStringFormat { dest, parts } => {
                use crate::mir::FStringPart;
                let i64_type = self.runtime_int_type();

                // Declare runtime functions — all i64 to match tagged-value ABI
                let string_new = module.get_function("rt_string_new").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
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

                // Start with empty string (ptr=0, len=0)
                let zero = i64_type.const_int(0, false);
                let empty_call = builder
                    .build_call(string_new, &[zero.into(), zero.into()], "empty_str")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
                let mut result = empty_call
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_type.const_int(0, false).into());

                for part in parts {
                    let part_str = match part {
                        FStringPart::Literal(s) => {
                            if s.is_empty() {
                                continue;
                            }
                            let str_val = self.context.const_string(s.as_bytes(), false);
                            let global = module.add_global(str_val.get_type(), None, "fstr");
                            global.set_initializer(&str_val);
                            global.set_constant(true);
                            global.set_linkage(inkwell::module::Linkage::Private);
                            let str_ptr = global.as_pointer_value();
                            // Convert ptr to i64 to match ABI
                            let str_ptr_int = builder
                                .build_ptr_to_int(str_ptr, i64_type, "fstr_ptr_int")
                                .map_err(|e| crate::error::factory::llvm_build_failed("ptrtoint", &e))?;
                            let str_len = i64_type.const_int(s.len() as u64, false);
                            let call = builder
                                .build_call(string_new, &[str_ptr_int.into(), str_len.into()], "lit_str")
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
                            call.try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                        FStringPart::Expr(vreg) => {
                            let val = self.get_vreg(vreg, vreg_map)?;
                            let coerced = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                            let call = builder
                                .build_call(value_to_string, &[coerced.into()], "expr_str")
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_to_string", &e))?;
                            call.try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                        FStringPart::ExprWithFormat(vreg, format_spec) => {
                            let value_format_fn = module.get_function("rt_value_format_string").unwrap_or_else(|| {
                                let fn_type =
                                    i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
                                module.add_function("rt_value_format_string", fn_type, None)
                            });
                            let val = self.get_vreg(vreg, vreg_map)?;
                            let coerced = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                            // Create format spec string constant
                            let spec_val = self.context.const_string(format_spec.as_bytes(), false);
                            let spec_global = module.add_global(spec_val.get_type(), None, "fmtspec");
                            spec_global.set_initializer(&spec_val);
                            spec_global.set_constant(true);
                            spec_global.set_linkage(inkwell::module::Linkage::Private);
                            let spec_ptr = spec_global.as_pointer_value();
                            let spec_ptr_int = builder
                                .build_ptr_to_int(spec_ptr, i64_type, "fmtspec_ptr_int")
                                .map_err(|e| crate::error::factory::llvm_build_failed("ptrtoint", &e))?;
                            let spec_len = i64_type.const_int(format_spec.len() as u64, false);
                            let call = builder
                                .build_call(
                                    value_format_fn,
                                    &[coerced.into(), spec_ptr_int.into(), spec_len.into()],
                                    "fmt_str",
                                )
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_value_format_string", &e))?;
                            call.try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                    };

                    let concat_call = builder
                        .build_call(string_concat, &[result.into(), part_str.into()], "concat")
                        .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_concat", &e))?;
                    result = concat_call
                        .try_as_basic_value()
                        .left()
                        .unwrap_or_else(|| i64_type.const_int(0, false).into());
                }

                vreg_map.insert(*dest, result);
            }

            // MethodCallVirtual — vtable-based dispatch; in tagged-value ABI just call receiver as function pointer
            MirInst::MethodCallVirtual {
                dest, receiver, args, ..
            } => {
                let i64_type = self.runtime_int_type();
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
            MirInst::MethodCallStatic {
                dest,
                receiver,
                func_name,
                args,
            } => {
                let i64_type = self.runtime_int_type();

                // Extract plain method name from qualified name (e.g., "text.len" -> "len")
                let method = func_name.rsplit('.').next().unwrap_or(func_name);

                // Special case: substring(start) → rt_slice(receiver, start, rt_len(receiver), 1)
                if method == "substring" && args.len() == 1 {
                    let recv_val = self.get_vreg(receiver, vreg_map)?;
                    let recv_casted = self.coerce_value_to_type(recv_val, Some(i64_type.into()), builder)?;
                    let start_val = self.get_vreg(&args[0], vreg_map)?;
                    let start_casted = self.coerce_value_to_type(start_val, Some(i64_type.into()), builder)?;
                    let len_fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    let len_func = module
                        .get_function("rt_len")
                        .unwrap_or_else(|| module.add_function("rt_len", len_fn_type, None));
                    let len_call = builder
                        .build_call(len_func, &[recv_casted.into()], "text_len")
                        .map_err(|e| crate::error::factory::llvm_build_failed("rt_len for substring", &e))?;
                    let end_val = len_call
                        .try_as_basic_value()
                        .left()
                        .unwrap_or_else(|| i64_type.const_int(0, false).into());
                    let step_val = i64_type.const_int(1, false);
                    // rt_slice(collection, start, end, step) takes 4 args
                    let slice_fn_type = i64_type.fn_type(
                        &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                        false,
                    );
                    let slice_func = module
                        .get_function("rt_slice")
                        .unwrap_or_else(|| module.add_function("rt_slice", slice_fn_type, None));
                    let slice_args = &[recv_casted.into(), start_casted.into(), end_val.into(), step_val.into()];
                    let declared_params = slice_func.get_type().get_param_types().len();
                    let slice_call = if declared_params != 4 {
                        let fn_ptr = slice_func.as_global_value().as_pointer_value();
                        builder
                            .build_indirect_call(slice_fn_type, fn_ptr, slice_args, "substr")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice for substring", &e))?
                    } else {
                        builder
                            .build_call(slice_func, slice_args, "substr")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice for substring", &e))?
                    };
                    if let Some(d) = dest {
                        if let Some(ret_val) = slice_call.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                    return Ok(());
                }

                if matches!(
                    method,
                    "to_u8"
                        | "to_i8"
                        | "to_u16"
                        | "to_i16"
                        | "to_u32"
                        | "to_i32"
                        | "to_u64"
                        | "to_i64"
                        | "to_int"
                ) {
                    let recv_val = self.get_vreg(receiver, vreg_map)?;
                    let int_type = match method {
                        "to_u8" | "to_i8" => self.context.i8_type(),
                        "to_u16" | "to_i16" => self.context.i16_type(),
                        "to_u32" | "to_i32" => self.context.i32_type(),
                        _ => self.context.i64_type(),
                    };
                    let converted = self.coerce_value_to_type(recv_val, Some(int_type.into()), builder)?;
                    if let Some(d) = dest {
                        vreg_map.insert(*d, converted);
                    }
                    return Ok(());
                }

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
                    "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => {
                        Some("rt_string_to_float")
                    }
                    "to_string" | "str" => Some("rt_to_string"),
                    // Index methods
                    "get" => Some("rt_index_get"),
                    "slice" => Some("rt_slice"),
                    // Note: "substring" is handled specially above (expands to rt_len + rt_slice)
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
                    // rt_slice requires exactly 4 args: (collection, start, end, step).
                    // Handle it specially to pad missing optional args with defaults
                    // (matching Cranelift behavior in try_compile_builtin_method_call).
                    if rt_name == "rt_slice" {
                        let coll = self.get_vreg(receiver, vreg_map)?;
                        let coll_i64 = self.coerce_value_to_type(coll, Some(i64_type.into()), builder)?;
                        let start_val = if !args.is_empty() {
                            let v = self.get_vreg(&args[0], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(0, false).into()
                        };
                        let end_val = if args.len() > 1 {
                            let v = self.get_vreg(&args[1], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(i64::MAX as u64, false).into()
                        };
                        let step_val = if args.len() > 2 {
                            let v = self.get_vreg(&args[2], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(1, false).into()
                        };
                        let slice_fn_type = i64_type.fn_type(
                            &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                            false,
                        );
                        let slice_fn = module
                            .get_function("rt_slice")
                            .unwrap_or_else(|| module.add_function("rt_slice", slice_fn_type, None));
                        let call_site = builder
                            .build_call(
                                slice_fn,
                                &[coll_i64.into(), start_val.into(), end_val.into(), step_val.into()],
                                "rtslice",
                            )
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice call", &e))?;
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                        return Ok(());
                    }
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
                    let returns_bool = matches!(
                        rt_name,
                        "rt_array_push"
                            | "rt_array_clear"
                            | "rt_array_reverse"
                            | "rt_array_sort"
                            | "rt_contains"
                            | "rt_dict_contains_key"
                            | "rt_is_none"
                            | "rt_is_some"
                            | "rt_array_any"
                            | "rt_array_all"
                    );
                    let fn_type = if returns_bool {
                        self.context.bool_type().fn_type(&param_types, false)
                    } else {
                        i64_type.fn_type(&param_types, false)
                    };
                    let rt_func = module
                        .get_function(rt_name)
                        .unwrap_or_else(|| module.add_function(rt_name, fn_type, None));
                    let declared_params = rt_func.get_type().get_param_types().len();
                    let call_site = if declared_params != all_args_vregs.len() {
                        let fn_ptr = rt_func.as_global_value().as_pointer_value();
                        builder
                            .build_indirect_call(fn_type, fn_ptr, &arg_vals, "rtcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt method call", &e))?
                    } else {
                        builder
                            .build_call(rt_func, &arg_vals, "rtcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt method call", &e))?
                    };
                    // For in-place mutating methods, return receiver
                    let in_place = matches!(method, "push" | "clear" | "reverse" | "sort");
                    if let Some(d) = dest {
                        if in_place {
                            let recv_val = self.get_vreg(receiver, vreg_map)?;
                            vreg_map.insert(*d, recv_val);
                        } else if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            let ret_val = if returns_bool {
                                self.coerce_value_to_type(ret_val, Some(i64_type.into()), builder)?
                            } else {
                                ret_val
                            };
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                } else {
                    // Fall back: resolve via import_map/use_map, then exact name, then suffix match
                    let mut all_args = vec![*receiver];
                    all_args.extend_from_slice(args);
                    let resolved = self
                        .use_map
                        .get(func_name)
                        .or_else(|| self.import_map.get(func_name))
                        .map(|s| s.as_str());
                    let dotted_name = func_name.replace("_dot_", ".");
                    let suffix_match = || -> Result<Option<inkwell::values::FunctionValue<'static>>, CompileError> {
                        let suffix = format!(".{}", dotted_name);
                        let mut func_opt = module.get_first_function();
                        let mut matches: Vec<(String, inkwell::values::FunctionValue)> = Vec::new();
                        while let Some(f) = func_opt {
                            let name = f.get_name().to_string_lossy().to_string();
                            if name.ends_with(&suffix) {
                                matches.push((name, f));
                            }
                            func_opt = f.get_next_function();
                        }
                        match matches.len() {
                            0 => Ok(None),
                            1 => Ok(matches.pop().map(|(_, f)| f)),
                            _ => {
                                matches.sort_by(|a, b| a.0.cmp(&b.0));
                                let names = matches.into_iter().map(|(name, _)| name).collect::<Vec<_>>().join(", ");
                                Err(CompileError::semantic(format!(
                                    "ambiguous LLVM method resolution for `{func_name}` via suffix `{suffix}`: {names}"
                                )))
                            }
                        }
                    };
                    let called_func = resolved
                        .and_then(|n| module.get_function(n))
                        .or_else(|| resolved.and_then(|n| module.get_function(&n.replace("_dot_", "."))))
                        .or_else(|| module.get_function(func_name))
                        .or_else(|| module.get_function(&dotted_name));
                    let called_func = if let Some(func) = called_func {
                        Some(func)
                    } else {
                        suffix_match()?
                    };

                    let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                        all_args.iter().map(|_| i64_type.into()).collect();
                    let fn_type = i64_type.fn_type(&param_types, false);
                    let fallback_name = resolved
                        .map(|n| n.replace("_dot_", "."))
                        .unwrap_or_else(|| dotted_name.clone());
                    let func = called_func
                        .unwrap_or_else(|| module.add_function(&fallback_name, fn_type, None));
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    for arg in &all_args {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                        arg_vals.push(casted.into());
                    }
                    let declared_params = func.get_type().get_param_types().len();
                    let call_site = if declared_params != all_args.len() {
                        let fn_ptr = func.as_global_value().as_pointer_value();
                        builder
                            .build_indirect_call(fn_type, fn_ptr, &arg_vals, "mcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("method call", &e))?
                    } else {
                        builder
                            .build_call(func, &arg_vals, "mcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("method call", &e))?
                    };
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                }
            }
            MirInst::BuiltinMethod {
                dest,
                receiver,
                receiver_type,
                method,
                args,
                ..
            } => {
                // Map builtin method calls to runtime functions (matching Cranelift backend)
                let i64_type = self.runtime_int_type();
                let receiver_val = self.get_vreg(receiver, vreg_map)?;
                let receiver_i64 = self.coerce_value_to_type(receiver_val, Some(i64_type.into()), builder)?;

                // Determine runtime function name based on receiver type and method
                let rt_name: Option<&str> = match (receiver_type.as_str(), method.as_str()) {
                    ("Array" | "array", "push") => Some("rt_array_push"),
                    ("Array" | "array", "len") => Some("rt_array_len"),
                    ("Array" | "array", "get") => Some("rt_index_get"),
                    ("Array" | "array", "set") => Some("rt_index_set"),
                    ("Array" | "array", "pop") => Some("rt_array_pop"),
                    ("Array" | "array", "clear") => Some("rt_array_clear"),
                    ("String" | "string", "len") => Some("rt_string_len"),
                    ("String" | "string", "concat") => Some("rt_string_concat"),
                    ("String" | "string", "starts_with") => Some("rt_string_starts_with"),
                    ("String" | "string", "ends_with") => Some("rt_string_ends_with"),
                    ("String" | "string", "contains")
                    | ("Array" | "array", "contains")
                    | ("Dict" | "dict", "contains") => Some("rt_contains"),
                    ("String" | "string", "substring") => Some("rt_string_substring"),
                    ("String" | "string", "split") => Some("rt_string_split"),
                    ("String" | "string", "trim") => Some("rt_string_trim"),
                    ("String" | "string", "replace") => Some("rt_string_replace"),
                    ("String" | "string", "index_of") => Some("rt_string_index_of"),
                    ("String" | "string", "to_upper") | ("String" | "string", "upper") => Some("rt_string_to_upper"),
                    ("String" | "string", "to_lower") | ("String" | "string", "lower") => Some("rt_string_to_lower"),
                    ("String" | "string", "char_at") => Some("rt_string_char_at"),
                    ("Dict" | "dict", "get") => Some("rt_index_get"),
                    ("Dict" | "dict", "set") => Some("rt_dict_set"),
                    ("Dict" | "dict", "len") => Some("rt_dict_len"),
                    ("Dict" | "dict", "clear") => Some("rt_dict_clear"),
                    ("Dict" | "dict", "keys") => Some("rt_dict_keys"),
                    ("Dict" | "dict", "values") => Some("rt_dict_values"),
                    ("Dict" | "dict", "contains_key") => Some("rt_dict_contains_key"),
                    ("Tuple" | "tuple", "get") => Some("rt_tuple_get"),
                    ("Tuple" | "tuple", "len") => Some("rt_tuple_len"),
                    ("Tuple" | "tuple", "set") => Some("rt_tuple_set"),
                    ("Array" | "array", "slice") | ("String" | "string", "slice") => Some("rt_slice"),
                    ("Array" | "array", "join") => Some("rt_array_join"),
                    ("Array" | "array", "sort") => Some("rt_array_sort"),
                    ("Array" | "array", "reverse") => Some("rt_array_reverse"),
                    ("Array" | "array", "filter") => Some("rt_array_filter"),
                    ("Array" | "array", "map") => Some("rt_array_map"),
                    ("Array" | "array", "each") | ("Array" | "array", "for_each") => Some("rt_array_each"),
                    ("Array" | "array", "find") => Some("rt_array_find"),
                    ("Array" | "array", "any") => Some("rt_array_any"),
                    ("Array" | "array", "all") => Some("rt_array_all"),
                    ("Array" | "array", "reduce") | ("Array" | "array", "fold") => Some("rt_array_reduce"),
                    _ => None,
                };

                if let Some(rt_fn_name) = rt_name {
                    // rt_slice: handle specially to pad missing optional args
                    if rt_fn_name == "rt_slice" {
                        let start_val = if !args.is_empty() {
                            let v = self.get_vreg(&args[0], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(0, false).into()
                        };
                        let end_val = if args.len() > 1 {
                            let v = self.get_vreg(&args[1], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(i64::MAX as u64, false).into()
                        };
                        let step_val = if args.len() > 2 {
                            let v = self.get_vreg(&args[2], vreg_map)?;
                            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
                        } else {
                            i64_type.const_int(1, false).into()
                        };
                        let slice_fn_type = i64_type.fn_type(
                            &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                            false,
                        );
                        let slice_fn = module
                            .get_function("rt_slice")
                            .unwrap_or_else(|| module.add_function("rt_slice", slice_fn_type, None));
                        let call_site = builder
                            .build_call(
                                slice_fn,
                                &[receiver_i64.into(), start_val.into(), end_val.into(), step_val.into()],
                                "bslice",
                            )
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice builtin call", &e))?;
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                        return Ok(());
                    }
                    // Build arg list: receiver + method args
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = vec![receiver_i64.into()];
                    for arg in args.iter() {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                        arg_vals.push(casted.into());
                    }
                    let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                        arg_vals.iter().map(|_| i64_type.into()).collect();
                    let fn_type = i64_type.fn_type(&param_types, false);
                    let rt_func = module
                        .get_function(rt_fn_name)
                        .unwrap_or_else(|| module.add_function(rt_fn_name, fn_type, None));
                    let call_site = builder
                        .build_call(rt_func, &arg_vals, "bcall")
                        .map_err(|e| crate::error::factory::llvm_build_failed("builtin call", &e))?;
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                } else {
                    // Fallback: try calling the method by name (may be user-defined)
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
                        let call_site = builder
                            .build_call(func, &arg_vals, "bcall")
                            .map_err(|e| crate::error::factory::llvm_build_failed("builtin call", &e))?;
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            } else {
                                vreg_map.insert(*d, i64_type.const_int(0, false).into());
                            }
                        }
                    } else {
                        // Method not found — return nil
                        if let Some(d) = dest {
                            vreg_map.insert(*d, i64_type.const_int(3, false).into());
                            // tagged nil
                        }
                    }
                }
            }
            MirInst::ExternMethodCall {
                dest,
                receiver,
                class_name,
                method_name,
                args,
                ..
            } => {
                // Compile as ClassName.method_name(receiver?, args...)
                let i64_type = self.runtime_int_type();
                let full_name = format!("{}.{}", class_name, method_name);
                let mut all_args: Vec<crate::mir::VReg> = Vec::new();
                if let Some(r) = receiver {
                    all_args.push(*r);
                }
                all_args.extend_from_slice(args);
                // Resolve via import_map/use_map first
                let resolved_full = self
                    .use_map
                    .get(full_name.as_str())
                    .or_else(|| self.import_map.get(full_name.as_str()));
                let resolved_method = self
                    .use_map
                    .get(method_name.as_str())
                    .or_else(|| self.import_map.get(method_name.as_str()));
                let dotted_full = full_name.replace("_dot_", ".");
                let dotted_method = method_name.replace("_dot_", ".");
                let func = resolved_full
                    .and_then(|n| module.get_function(n))
                    .or_else(|| resolved_full.and_then(|n| module.get_function(&n.replace("_dot_", "."))))
                    .or_else(|| module.get_function(&full_name))
                    .or_else(|| module.get_function(&dotted_full))
                    .or_else(|| resolved_method.and_then(|n| module.get_function(n)))
                    .or_else(|| resolved_method.and_then(|n| module.get_function(&n.replace("_dot_", "."))))
                    .or_else(|| module.get_function(method_name))
                    .or_else(|| module.get_function(&dotted_method));
                let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    all_args.iter().map(|_| i64_type.into()).collect();
                let fn_type = i64_type.fn_type(&param_types, false);
                let fallback_name = resolved_full
                    .map(|n| n.replace("_dot_", "."))
                    .or_else(|| resolved_method.map(|n| n.replace("_dot_", ".")))
                    .unwrap_or_else(|| dotted_full.clone());
                let func = func.unwrap_or_else(|| module.add_function(&fallback_name, fn_type, None));
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in &all_args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                    arg_vals.push(casted.into());
                }
                let declared_params = func.get_type().get_param_types().len();
                let call_site = if declared_params != all_args.len() {
                    let fn_ptr = func.as_global_value().as_pointer_value();
                    builder
                        .build_indirect_call(fn_type, fn_ptr, &arg_vals, "ecall")
                        .map_err(|e| crate::error::factory::llvm_build_failed("extern call", &e))?
                } else {
                    builder
                        .build_call(func, &arg_vals, "ecall")
                        .map_err(|e| crate::error::factory::llvm_build_failed("extern call", &e))?
                };
                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(*d, ret_val);
                    } else {
                        vreg_map.insert(*d, i64_type.const_int(0, false).into());
                    }
                }
            }

            // Global variable access
            MirInst::GlobalLoad { dest, global_name, ty } => {
                let i64_type = self.runtime_int_type();
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
                let i64_type = self.runtime_int_type();
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
            MirInst::GetElementPtr { dest, .. } | MirInst::NeighborLoad { dest, .. } => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(*dest, default_val.into());
            }
            MirInst::Wait { dest, .. } => {
                if let Some(d) = dest {
                    let default_val = self.runtime_int_type().const_int(0, false);
                    vreg_map.insert(*d, default_val.into());
                }
            }
            MirInst::GlobalStore { .. } => {}
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
            .unwrap_or_else(|| self.runtime_int_type().const_int(0, false).into()))
    }

    #[cfg(feature = "llvm")]
    fn get_vreg_val(
        &self,
        vreg: &crate::mir::VReg,
        vreg_map: &VRegMap,
        i64_type: inkwell::types::IntType<'static>,
    ) -> inkwell::values::BasicValueEnum<'static> {
        vreg_map
            .get(vreg)
            .copied()
            .unwrap_or_else(|| i64_type.const_int(0, false).into())
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

#[cfg(all(test, feature = "llvm"))]
mod tests {
    use super::*;
    use simple_common::target::{Target, TargetArch, TargetOS};

    #[test]
    fn test_riscv32_float_boxing_uses_runtime_helpers() {
        let target = Target::new(TargetArch::Riscv32, TargetOS::SimpleOS);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("rv32_float_boxing").unwrap();

        {
            let module_ref = backend.module.borrow();
            let module = module_ref.as_ref().unwrap();
            let builder_ref = backend.builder.borrow();
            let builder = builder_ref.as_ref().unwrap();
            let fn_type = backend.context.void_type().fn_type(&[], false);
            let func = module.add_function("test", fn_type, None);
            let block = backend.context.append_basic_block(func, "entry");
            builder.position_at_end(block);

            let float_val = backend.context.f64_type().const_float(1.5);
            let boxed = backend
                .build_box_float_value(float_val.into(), builder, module)
                .unwrap();
            let unboxed = backend
                .build_unbox_float_value(boxed.into(), builder, module)
                .unwrap();
            let _ = unboxed;
            builder.build_return(None).unwrap();
        }

        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("call i32 @rt_box_float(double"));
        assert!(ir.contains("call double @rt_unbox_float(i32"));
        assert!(!ir.contains("bitcast i32"));
        backend.verify().unwrap();
    }
}
