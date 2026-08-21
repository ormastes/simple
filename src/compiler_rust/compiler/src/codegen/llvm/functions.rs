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

#[cfg(feature = "llvm")]
type VRegTypes = std::collections::HashMap<crate::mir::VReg, crate::hir::TypeId>;

/// Fallback VRegMap when LLVM is not enabled
#[cfg(not(feature = "llvm"))]
type VRegMap = std::collections::HashMap<crate::mir::VReg, ()>;

#[cfg(feature = "llvm")]
fn unit_bits_to_type_id(bits: u8, signed: bool) -> Option<crate::hir::TypeId> {
    use crate::hir::TypeId;

    match (bits, signed) {
        (8, true) => Some(TypeId::I8),
        (16, true) => Some(TypeId::I16),
        (32, true) => Some(TypeId::I32),
        (64, true) => Some(TypeId::I64),
        (8, false) => Some(TypeId::U8),
        (16, false) => Some(TypeId::U16),
        (32, false) => Some(TypeId::U32),
        (64, false) => Some(TypeId::U64),
        _ => None,
    }
}

#[cfg(feature = "llvm")]
fn binop_result_type(op: crate::hir::BinOp, lhs_ty: Option<crate::hir::TypeId>) -> Option<crate::hir::TypeId> {
    use crate::hir::{BinOp, TypeId};

    match op {
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => Some(TypeId::BOOL),
        BinOp::Is | BinOp::In | BinOp::NotIn => Some(TypeId::BOOL),
        BinOp::And | BinOp::Or | BinOp::AndSuspend | BinOp::OrSuspend => Some(TypeId::BOOL),
        _ => lhs_ty,
    }
}

/// Source-level spelling of a primitive `TypeId`, used to disambiguate method
/// symbols that share a leaf name but differ in receiver type (`f64.to_f32` vs
/// `i64.to_f32`). Returns `None` for aggregate/user types, whose `TypeId` is an
/// interned index and carries no spelling here.
#[cfg(feature = "llvm")]
fn primitive_type_symbol_name(ty: crate::hir::TypeId) -> Option<&'static str> {
    use crate::hir::TypeId;

    Some(match ty {
        TypeId::BOOL => "bool",
        TypeId::I8 => "i8",
        TypeId::I16 => "i16",
        TypeId::I32 => "i32",
        TypeId::I64 => "i64",
        TypeId::U8 => "u8",
        TypeId::U16 => "u16",
        TypeId::U32 => "u32",
        TypeId::U64 => "u64",
        TypeId::F32 => "f32",
        TypeId::F64 => "f64",
        TypeId::STRING => "string",
        TypeId::CHAR => "char",
        _ => return None,
    })
}

#[cfg(feature = "llvm")]
fn build_vreg_types(
    func: &MirFunction,
    function_return_types: &std::collections::HashMap<String, crate::hir::TypeId>,
) -> VRegTypes {
    use crate::hir::{TypeId, UnaryOp};
    use crate::mir::MirInst;

    let mut types_map = VRegTypes::new();

    for (i, param) in func.params.iter().enumerate() {
        types_map.insert(crate::mir::VReg(i as u32), param.ty);
    }

    for block in &func.blocks {
        for inst in &block.instructions {
            match inst {
                MirInst::ConstInt { dest, .. } => {
                    types_map.insert(*dest, TypeId::I64);
                }
                MirInst::ConstFloat { dest, .. } => {
                    types_map.insert(*dest, TypeId::F64);
                }
                MirInst::ConstBool { dest, .. } => {
                    types_map.insert(*dest, TypeId::BOOL);
                }
                MirInst::Copy { dest, src } => {
                    if let Some(&ty) = types_map.get(src) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::BinOp { dest, op, left, .. } => {
                    if let Some(ty) = binop_result_type(*op, types_map.get(left).copied()) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::UnaryOp { dest, op, operand } => {
                    let ty = match op {
                        UnaryOp::Not => Some(TypeId::BOOL),
                        _ => types_map.get(operand).copied(),
                    };
                    if let Some(ty) = ty {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::Cast { dest, to_ty, .. } => {
                    types_map.insert(*dest, *to_ty);
                }
                MirInst::Load { dest, ty, .. } | MirInst::GlobalLoad { dest, ty, .. } => {
                    types_map.insert(*dest, *ty);
                }
                MirInst::GcAlloc { dest, ty } => {
                    types_map.insert(*dest, *ty);
                }
                MirInst::StructInit { dest, type_id, .. } => {
                    types_map.insert(*dest, *type_id);
                }
                MirInst::FieldGet { dest, field_type, .. } => {
                    types_map.insert(*dest, *field_type);
                }
                MirInst::Call {
                    dest: Some(dest),
                    target,
                    ..
                } => {
                    if let Some(ty) = function_return_types.get(target.name()) {
                        types_map.insert(*dest, *ty);
                    }
                }
                MirInst::Call { dest: None, .. } => {}
                // Instance-method calls had NO arm here at all, so a
                // user-defined `fn getf(..) -> f64` left its dest VReg untyped
                // and float binops lowered to INTEGER ops on the IEEE-754 bits
                // (see the matching fix + full write-up in instr/body.rs).
                // `MethodCallStatic` carries no `return_type` field (unlike
                // `MethodCallVirtual` / `IndirectCall` just below), so the type
                // has to be recovered from `function_return_types`, which MIR
                // keys by the same `"Class.method"` name the instruction uses.
                MirInst::MethodCallStatic {
                    dest: Some(dest),
                    func_name,
                    ..
                } => {
                    if let Some(ty) = function_return_types.get(func_name.as_str()) {
                        if matches!(ty, &TypeId::F64 | &TypeId::F32) {
                            types_map.insert(*dest, *ty);
                        }
                    }
                }
                MirInst::IndirectCall {
                    dest: Some(dest),
                    return_type,
                    ..
                }
                | MirInst::MethodCallVirtual {
                    dest: Some(dest),
                    return_type,
                    ..
                } => {
                    types_map.insert(*dest, *return_type);
                }
                MirInst::IndirectCall { dest: None, .. } | MirInst::MethodCallVirtual { dest: None, .. } => {}
                MirInst::UnitWiden {
                    dest, to_bits, signed, ..
                }
                | MirInst::UnitNarrow {
                    dest, to_bits, signed, ..
                } => {
                    if let Some(ty) = unit_bits_to_type_id(*to_bits, *signed) {
                        types_map.insert(*dest, ty);
                    }
                }
                MirInst::UnitSaturate { dest, .. } => {
                    types_map.insert(*dest, TypeId::I64);
                }
                MirInst::BoxInt { dest, .. } | MirInst::UnboxInt { dest, .. } => {
                    types_map.insert(*dest, TypeId::I64);
                }
                MirInst::BoxFloat { dest, .. } | MirInst::UnboxFloat { dest, .. } => {
                    types_map.insert(*dest, TypeId::F64);
                }
                _ => {}
            }
        }
    }

    types_map
}

#[cfg(feature = "llvm")]
fn vreg_is_signed(vreg_types: &VRegTypes, v: crate::mir::VReg) -> Option<bool> {
    use crate::hir::TypeId;

    match vreg_types.get(&v).copied()? {
        TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 => Some(true),
        TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64 => Some(false),
        _ => None,
    }
}

#[cfg(feature = "llvm")]
fn implicit_local_param_slots(func: &MirFunction) -> usize {
    use crate::mir::MirInst;

    let declared_slots = func.params.len() + func.locals.len();
    let mut max_local_index = None;
    for block in &func.blocks {
        for inst in &block.instructions {
            if let MirInst::LocalAddr { local_index, .. } = inst {
                max_local_index = Some(max_local_index.map_or(*local_index, |cur: usize| cur.max(*local_index)));
            }
        }
    }

    match max_local_index {
        Some(max_idx) if max_idx + 1 > declared_slots => (max_idx + 1) - declared_slots,
        _ => 0,
    }
}

impl LlvmBackend {
    /// Box a membership-test needle (`.contains(x)` / `.has(k)` / `x in c`) so
    /// an int/bool/float key compares equal to what the tagged store path
    /// recorded (dict/array stores box keys/elements via `rt_value_*`, i.e.
    /// `k<<3|tag`). Without this, `rt_contains` receives a RAW i64 and the
    /// membership answer is wrong in BOTH directions (raw `k` never matches
    /// stored `k<<3`; raw `k<<3` falsely matches stored `k`).
    /// Mirrors the Cranelift `wrap_value` gate (codegen/instr/methods.rs):
    /// wrap ONLY when the vreg is statically a raw primitive; anything unknown
    /// or heap-typed (text, arrays, already-boxed values) passes through
    /// untouched, so double-boxing is impossible.
    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn build_wrap_membership_needle(
        &self,
        vreg: crate::mir::VReg,
        val: inkwell::values::BasicValueEnum<'static>,
        vreg_types: &VRegTypes,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::TypeId;
        let i64_type = self.runtime_int_type();
        let helper_name = match vreg_types.get(&vreg).copied() {
            Some(TypeId::BOOL) => "rt_value_bool",
            Some(
                TypeId::I8
                | TypeId::I16
                | TypeId::I32
                | TypeId::I64
                | TypeId::U8
                | TypeId::U16
                | TypeId::U32
                | TypeId::U64,
            ) => "rt_value_int",
            Some(TypeId::F32 | TypeId::F64) => {
                return Ok(self.build_box_float_value(val, builder, module)?.into());
            }
            _ => return Ok(val),
        };
        let arg = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        let func = module
            .get_function(helper_name)
            .unwrap_or_else(|| module.add_function(helper_name, fn_type, None));
        let call = builder
            .build_call(func, &[arg.into()], "wrap_needle")
            .map_err(|e| crate::error::factory::llvm_build_failed("wrap membership needle", &e))?;
        Ok(call
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_type.const_int(0, false).into()))
    }

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
                // f32 values (e.g. struct fields typed f32) must be widened
                // first: bitcasting f32 straight to i64 is a size mismatch.
                let f64_type = self.context_ref().f64_type();
                let fv = val.into_float_value();
                let fv = if fv.get_type() == f64_type {
                    fv
                } else {
                    builder
                        .build_float_ext(fv, f64_type, "box_fext")
                        .map_err(|e| crate::error::factory::llvm_build_failed("float_ext", &e))?
                };
                builder
                    .build_bit_cast(fv, rv_type, "f2i")
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

        let f64_type = self.context_ref().f64_type();
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

        // `rt_box_float` NEVER EXISTED in any runtime (2026-08-01): there is no
        // `pub extern "C" fn rt_box_float` under src/compiler_rust/runtime and no
        // `rt_box_float(` definition in src/runtime/runtime_native.c — only a
        // stale comment mentions the name. The real f64 tagging helper is
        // `rt_value_float`, which IS defined in BOTH runtimes. Same defect and
        // same fix as the Cranelift `wrap_value` path (see
        // codegen/instr/methods.rs), where emitting the nonexistent
        // `rt_box_int`/`rt_box_float` made the JIT report "unresolved external
        // symbol" and silently drop the whole module to the interpreter.
        let fn_type = rv_type.fn_type(&[f64_type.into()], false);
        let func = module
            .get_function("rt_value_float")
            .unwrap_or_else(|| module.add_function("rt_value_float", fn_type, None));
        let call = builder
            .build_call(func, &[f64_val.into()], "rt_value_float")
            .map_err(|e| crate::error::factory::llvm_build_failed("call rt_value_float", &e))?;
        let ret = call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::semantic("rt_value_float returned no value".to_string()))?
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
        let f64_type = self.context_ref().f64_type();

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

        // `rt_unbox_float` never existed either — sibling of the `rt_box_float`
        // defect above. It has ZERO mentions anywhere under
        // src/compiler_rust/runtime or src/runtime. The real untagging helper is
        // `rt_value_as_float`, defined in BOTH runtimes
        // (`rt_value_as_float(RuntimeValue) -> f64` / `double
        // rt_value_as_float(int64_t)`), matching this `(rv) -> f64` shape.
        let fn_type = f64_type.fn_type(&[rv_type.into()], false);
        let func = module
            .get_function("rt_value_as_float")
            .unwrap_or_else(|| module.add_function("rt_value_as_float", fn_type, None));
        let call = builder
            .build_call(func, &[int_val.into()], "rt_value_as_float")
            .map_err(|e| crate::error::factory::llvm_build_failed("call rt_value_as_float", &e))?;
        Ok(call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::semantic("rt_value_as_float returned no value".to_string()))?
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

        let resolved_name = if func.blocks.is_empty() {
            self.use_map
                .get(&func.name)
                .or_else(|| self.import_map.get(&func.name))
                .map(|s| s.as_str())
                .unwrap_or(&func.name)
        } else {
            func.name.as_str()
        };

        // Get the function that was forward-declared in the compile() pass
        // If it doesn't exist, create it (for backwards compatibility)
        let function = module.get_function(resolved_name).unwrap_or_else(|| {
            let i64_type = self.runtime_int_type();
            let implicit_slots = implicit_local_param_slots(func);
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                std::iter::repeat_n(i64_type.into(), implicit_slots)
                    .chain(func.params.iter().map(|_| i64_type.into()))
                    .collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(resolved_name, fn_type, None)
        });

        // Create basic blocks for each MIR block
        let mut llvm_blocks = HashMap::new();
        for block in &func.blocks {
            let bb = self
                .context_ref()
                .append_basic_block(function, &format!("bb{}", block.id.0));
            llvm_blocks.insert(block.id, bb);
        }

        // Map virtual registers to LLVM values (used within each block)
        let mut vreg_map: VRegMap = HashMap::new();
        let function_return_types = self.function_return_types.borrow();
        let vreg_types = build_vreg_types(func, &function_return_types);

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
                crate::mir::Terminator::Switch { discriminant, .. } => {
                    all_vregs.insert(*discriminant);
                }
                _ => {}
            }
        }

        // Allocate stack space for parameters and locals at the entry block
        let mut local_allocas: HashMap<usize, inkwell::values::PointerValue<'static>> = HashMap::new();
        if !func.blocks.is_empty() {
            let entry_bb = llvm_blocks[&func.blocks[0].id];
            builder.position_at_end(entry_bb);

            let implicit_slots = implicit_local_param_slots(func);

            for slot in 0..implicit_slots {
                let alloca = builder
                    .build_alloca(self.runtime_int_type(), &format!("implicit_local_{slot}"))
                    .map_err(|e| crate::error::factory::llvm_build_failed("implicit param alloca", &e))?;
                local_allocas.insert(slot, alloca);
            }

            // Create allocas for parameters (index 0..param_count)
            for (i, param) in func.params.iter().enumerate() {
                let param_ty = self.llvm_type(&param.ty)?;
                let alloca = builder
                    .build_alloca(param_ty, &param.name)
                    .map_err(|e| crate::error::factory::llvm_build_failed("param alloca", &e))?;
                local_allocas.insert(implicit_slots + i, alloca);
            }

            // Create allocas for locals (index param_count..param_count+local_count)
            let param_count = implicit_slots + func.params.len();
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
            for i in 0..implicit_slots {
                if let Some(llvm_param) = function.get_nth_param(i as u32) {
                    if let Some(&alloca) = local_allocas.get(&i) {
                        builder
                            .build_store(alloca, llvm_param)
                            .map_err(|e| crate::error::factory::llvm_build_failed("store implicit param", &e))?;
                    }
                }
            }
            for (i, _param) in func.params.iter().enumerate() {
                let llvm_index = implicit_slots + i;
                if let Some(llvm_param) = function.get_nth_param(llvm_index as u32) {
                    if let Some(&alloca) = local_allocas.get(&llvm_index) {
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

            if let Some(meta) = func
                .outlined_bodies
                .values()
                .find(|meta| meta.is_lambda && !meta.lambda_capture_local_indices.is_empty())
            {
                if let Some(ctx_param) = function.get_nth_param(0) {
                    let i8_type = self.context_ref().i8_type();
                    let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                    let i64_type = self.runtime_int_type();
                    let ctx_ptr = match ctx_param {
                        inkwell::values::BasicValueEnum::PointerValue(ptr) => builder
                            .build_pointer_cast(ptr, i8_ptr_type, "lambda_ctx_ptr")
                            .map_err(|e| crate::error::factory::llvm_cast_failed("cast lambda ctx", &e))?,
                        inkwell::values::BasicValueEnum::IntValue(iv) => builder
                            .build_int_to_ptr(iv, i8_ptr_type, "lambda_ctx_ptr")
                            .map_err(|e| crate::error::factory::llvm_build_failed("lambda ctx int_to_ptr", &e))?,
                        _ => {
                            return Err(crate::error::factory::llvm_build_failed(
                                "lambda ctx",
                                &"unsupported ctx parameter kind",
                            ))
                        }
                    };

                    for (capture_index, local_index) in meta.lambda_capture_local_indices.iter().enumerate() {
                        let Some(&alloca) = local_allocas.get(local_index) else {
                            continue;
                        };
                        let offset = 8 + (capture_index as u64 * 8);
                        let offset_val = self.context_ref().i32_type().const_int(offset, false);
                        let field_ptr = unsafe {
                            builder
                                .build_gep(i8_type, ctx_ptr, &[offset_val], "lambda_capture_ptr")
                                .map_err(|e| crate::error::factory::llvm_build_failed("lambda capture gep", &e))?
                        };
                        let typed_ptr = builder
                            .build_pointer_cast(
                                field_ptr,
                                self.context_ref().ptr_type(inkwell::AddressSpace::default()),
                                "lambda_capture_typed_ptr",
                            )
                            .map_err(|e| crate::error::factory::llvm_cast_failed("cast lambda capture ptr", &e))?;
                        let loaded = builder
                            .build_load(i64_type, typed_ptr, "lambda_capture")
                            .map_err(|e| crate::error::factory::llvm_build_failed("load lambda capture", &e))?;
                        builder
                            .build_store(alloca, loaded)
                            .map_err(|e| crate::error::factory::llvm_build_failed("store lambda capture", &e))?;
                    }
                }
            }
        }

        // Map function parameters to virtual registers
        for (i, _param) in func.params.iter().enumerate() {
            let implicit_slots = implicit_local_param_slots(func);
            if let Some(llvm_param) = function.get_nth_param((implicit_slots + i) as u32) {
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
                    crate::mir::Terminator::Switch { discriminant, .. } => {
                        if !seen_defs.contains(discriminant) {
                            live_in.insert(*discriminant);
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

                self.compile_instruction(inst, &mut vreg_map, &local_allocas, &vreg_types, builder, module)?;

                // Store any newly defined vreg to its alloca (for cross-block access)
                if let Some(d) = inst.dest() {
                    if let (Some(&alloca), Some(&val)) = (vreg_allocas.get(&d), vreg_map.get(&d)) {
                        let rv_type = self.runtime_int_type();
                        let i64_val = self
                            .coerce_value_to_type(val, Some(rv_type.into()), builder)
                            .unwrap_or(val);
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
                crate::mir::Terminator::Switch { discriminant, .. } => {
                    if !vreg_map.contains_key(discriminant) {
                        if let Some(&alloca) = vreg_allocas.get(discriminant) {
                            if let Ok(val) = builder.build_load(i64_type, alloca, &format!("v{}", discriminant.0)) {
                                vreg_map.insert(*discriminant, val);
                            }
                        }
                    }
                }
                _ => {}
            }
            self.compile_terminator(&block.terminator, func.return_type, &llvm_blocks, &vreg_map, builder)?;
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
        vreg_types: &VRegTypes,
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
            MirInst::AggregateCopy { dest, src, byte_size, deep_fields, .. } => {
                self.compile_aggregate_copy(*dest, *src, *byte_size, deep_fields, vreg_map, builder)?;
            }
            MirInst::BinOp { dest, op, left, right } => {
                let left_val = self.get_vreg(left, vreg_map)?;
                let right_val = self.get_vreg(right, vreg_map)?;
                let lhs_ty = vreg_types.get(left).copied();
                let rhs_ty = vreg_types.get(right).copied();
                let result = self.compile_binop(
                    *op,
                    left_val,
                    right_val,
                    builder,
                    module,
                    vreg_is_signed(vreg_types, *left),
                    lhs_ty,
                    rhs_ty,
                )?;
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
                let result = self.compile_cast(source_val, from_ty, to_ty, builder, module)?;
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
                self.compile_call(*dest, target, args, vreg_map, vreg_types, builder, module)?;
            }
            MirInst::InlineAsm { instructions, .. } => {
                let fn_type = self.context_ref().void_type().fn_type(&[], false);
                let asm = self.context_ref().create_inline_asm(
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
                dest, func_name, args, ..
            } => {
                self.compile_interp_call(*dest, func_name, args, vreg_map, vreg_types, builder, module)?;
            }
            MirInst::InterpEval { dest, expr_index } => {
                self.compile_interp_eval(*dest, *expr_index as usize, vreg_map, builder, module)?;
            }

            // Objects
            MirInst::StructInit {
                dest,
                struct_size,
                vtable_symbol,
                field_offsets,
                field_types,
                field_values,
                ..
            } => {
                self.compile_struct_init(
                    *dest,
                    *struct_size,
                    vtable_symbol.as_deref(),
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
                owner_has_vtable,
                ..
            } => {
                self.compile_field_get(
                    *dest,
                    *object,
                    *byte_offset + u32::from(owner_has_vtable == &Some(true)) * 8,
                    field_type,
                    vreg_map,
                    builder,
                )?;
            }
            MirInst::FieldSet {
                object,
                byte_offset,
                field_type,
                value,
                owner_has_vtable,
                ..
            } => {
                self.compile_field_set(
                    *object,
                    *byte_offset + u32::from(owner_has_vtable == &Some(true)) * 8,
                    field_type,
                    *value,
                    vreg_map,
                    builder,
                )?;
            }
            MirInst::ClosureCreate {
                dest,
                func_name,
                closure_size,
                capture_offsets,
                capture_types,
                captures,
                lambda_params: _,
                body_block: _,
                return_type: _,
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

            // SIMD instructions supported by the LLVM runtime-delegating emitter.
            #[cfg(feature = "llvm")]
            MirInst::VecLit { .. }
            | MirInst::VecSum { .. }
            | MirInst::VecProduct { .. }
            | MirInst::VecMin { .. }
            | MirInst::VecMax { .. }
            | MirInst::VecAll { .. }
            | MirInst::VecAny { .. }
            | MirInst::VecExtract { .. }
            | MirInst::VecWith { .. }
            | MirInst::VecSqrt { .. }
            | MirInst::VecAbs { .. }
            | MirInst::VecFloor { .. }
            | MirInst::VecCeil { .. }
            | MirInst::VecRound { .. }
            | MirInst::VecShuffle { .. }
            | MirInst::VecBlend { .. }
            | MirInst::VecSelect { .. }
            | MirInst::VecLoad { .. }
            | MirInst::VecStore { .. }
            | MirInst::VecGather { .. }
            | MirInst::VecScatter { .. }
            | MirInst::VecFma { .. }
            | MirInst::VecRecip { .. }
            | MirInst::VecMaskedLoad { .. }
            | MirInst::VecMaskedStore { .. }
            | MirInst::VecMinVec { .. }
            | MirInst::VecMaxVec { .. }
            | MirInst::VecClamp { .. } => {
                self.compile_emitter_simd_instruction(inst, vreg_map, local_allocas, builder, module)?;
            }

            // Non-LLVM builds keep the historical SIMD placeholder behavior.
            #[cfg(not(feature = "llvm"))]
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

            #[cfg(not(feature = "llvm"))]
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
                            let global_val = self.context_ref().const_string(bytes, false);
                            let global = module.add_global(global_val.get_type(), None, "pat_str_const");
                            global.set_initializer(&global_val);
                            global.set_constant(true);
                            let str_ptr = builder
                                .build_pointer_cast(
                                    global.as_pointer_value(),
                                    self.context_ref().ptr_type(inkwell::AddressSpace::default()),
                                    "str_ptr",
                                )
                                .map_err(|e| format!("pattern str ptr: {e}"))?;
                            let str_ptr_int = builder
                                .build_ptr_to_int(str_ptr, i64_type, "str_ptr_int")
                                .map_err(|e| format!("pattern ptrtoint: {e}"))?;
                            let str_len = i64_type.const_int(bytes.len() as u64, false);
                            // rt_string_new_literal(ptr, len) -> RuntimeValue.
                            // Interned: this pattern test re-executes per match
                            // evaluation; per-eval rt_string_new leaked one
                            // registered string per execution on the no-GC tier.
                            let rt_string_new = module.get_function("rt_string_new_literal").unwrap_or_else(|| {
                                let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                                module.add_function("rt_string_new_literal", fn_type, None)
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
                    crate::mir::MirPattern::Variant {
                        enum_name,
                        variant_name,
                        ..
                    } => {
                        // Runtime type and discriminant must both match.
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
                        let rt_enum_id = module.get_function("rt_enum_id").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_enum_id", fn_type, None)
                        });
                        let enum_id = builder
                            .build_call(rt_enum_id, &[subject_val.into()], "enum_id")
                            .map_err(|e| format!("pattern enum id: {e}"))?
                            .try_as_basic_value()
                            .left()
                            .unwrap_or_else(|| i64_type.const_int(u64::MAX, false).into())
                            .into_int_value();
                        let expected = {
                            use std::collections::hash_map::DefaultHasher;
                            use std::hash::{Hash, Hasher};
                            let mut hasher = DefaultHasher::new();
                            variant_name.hash(&mut hasher);
                            (hasher.finish() & 0xFFFFFFFF) as u64
                        };
                        let expected_val = i64_type.const_int(expected, false);
                        let disc_cmp = builder
                            .build_int_compare(inkwell::IntPredicate::EQ, disc, expected_val, "pat_var_eq")
                            .map_err(|e| format!("pattern var icmp: {e}"))?;
                        let expected_id = i64_type.const_int(
                            u64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
                            false,
                        );
                        let id_cmp = builder
                            .build_int_compare(inkwell::IntPredicate::EQ, enum_id, expected_id, "pat_enum_eq")
                            .map_err(|e| format!("pattern enum id icmp: {e}"))?;
                        let cmp = builder
                            .build_and(disc_cmp, id_cmp, "pat_enum_variant_eq")
                            .map_err(|e| format!("pattern enum and: {e}"))?;
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
                let mut result = if binding.path.is_empty() {
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
                if vreg_types.get(dest).copied() == Some(crate::hir::TypeId::U64) {
                    let raw_fn = module.get_function("rt_value_as_u64").unwrap_or_else(|| {
                        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                        module.add_function("rt_value_as_u64", fn_type, None)
                    });
                    result = builder
                        .build_call(raw_fn, &[result.into()], "u64_payload")
                        .map_err(|e| CompileError::Semantic(format!("u64 payload call: {e}")))?
                        .try_as_basic_value()
                        .left()
                        .unwrap_or(result);
                }
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
            MirInst::EnumUnit {
                dest,
                enum_name,
                variant_name,
            } => {
                // rt_enum_new(enum_id: u32, discriminant: u32, payload: RuntimeValue) -> RuntimeValue
                let i64_t = self.runtime_int_type();
                let i32_t = self.context_ref().i32_type();
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
                let enum_id_val = i32_t.const_int(
                    u64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
                    false,
                );
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
                enum_name,
                variant_name,
                payload,
            } => {
                let i64_t = self.runtime_int_type();
                let i32_t = self.context_ref().i32_type();
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
                let enum_id_val = i32_t.const_int(
                    u64::from(crate::codegen::shared::enum_runtime_type_id(enum_name)),
                    false,
                );
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
                let i32_t = self.context_ref().i32_type();
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
                let i32_t = self.context_ref().i32_type();
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
                let i32_t = self.context_ref().i32_type();
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
                let i32_t = self.context_ref().i32_type();
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
                let i32_t = self.context_ref().i32_type();
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

            MirInst::UnitBoundCheck { .. } => {}
            MirInst::UnitWiden { dest, value, .. } => {
                let val = self.get_vreg(value, vreg_map)?;
                vreg_map.insert(*dest, val);
            }
            MirInst::UnitNarrow {
                dest,
                value,
                to_bits,
                signed,
                overflow,
                ..
            } => {
                let val = self
                    .coerce_value_to_type(
                        self.get_vreg(value, vreg_map)?,
                        Some(self.runtime_int_type().into()),
                        builder,
                    )?
                    .into_int_value();
                let narrowed = match overflow {
                    crate::mir::UnitOverflowBehavior::Wrap => {
                        if *to_bits >= 64 {
                            val
                        } else {
                            let mask = (1u64 << *to_bits) - 1;
                            builder
                                .build_and(val, self.runtime_int_type().const_int(mask, false), "unit_wrap")
                                .map_err(|e| crate::error::factory::llvm_build_failed("unit wrap", &e))?
                        }
                    }
                    crate::mir::UnitOverflowBehavior::Saturate => {
                        let (min, max) = if *signed {
                            if *to_bits >= 64 {
                                (i64::MIN, i64::MAX)
                            } else {
                                (-(1i64 << (*to_bits - 1)), (1i64 << (*to_bits - 1)) - 1)
                            }
                        } else if *to_bits >= 63 {
                            (0, i64::MAX)
                        } else {
                            (0, (1i64 << *to_bits) - 1)
                        };
                        let min_v = self.runtime_int_type().const_int(min as u64, true);
                        let max_v = self.runtime_int_type().const_int(max as u64, true);
                        let gt_max = builder
                            .build_int_compare(inkwell::IntPredicate::SGT, val, max_v, "unit_gt_max")
                            .map_err(|e| crate::error::factory::llvm_build_failed("unit gt max", &e))?;
                        let clamped_high = builder
                            .build_select(gt_max, max_v, val, "unit_clamp_high")
                            .map_err(|e| crate::error::factory::llvm_build_failed("unit clamp high", &e))?
                            .into_int_value();
                        let lt_min = builder
                            .build_int_compare(inkwell::IntPredicate::SLT, clamped_high, min_v, "unit_lt_min")
                            .map_err(|e| crate::error::factory::llvm_build_failed("unit lt min", &e))?;
                        builder
                            .build_select(lt_min, min_v, clamped_high, "unit_clamp")
                            .map_err(|e| crate::error::factory::llvm_build_failed("unit clamp", &e))?
                            .into_int_value()
                    }
                    crate::mir::UnitOverflowBehavior::Default | crate::mir::UnitOverflowBehavior::Checked => val,
                };
                vreg_map.insert(*dest, narrowed.into());
            }
            MirInst::UnitSaturate { dest, value, min, max } => {
                let val = self
                    .coerce_value_to_type(
                        self.get_vreg(value, vreg_map)?,
                        Some(self.runtime_int_type().into()),
                        builder,
                    )?
                    .into_int_value();
                let min_v = self.runtime_int_type().const_int(*min as u64, true);
                let max_v = self.runtime_int_type().const_int(*max as u64, true);
                let gt_max = builder
                    .build_int_compare(inkwell::IntPredicate::SGT, val, max_v, "unit_gt_max")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unit gt max", &e))?;
                let clamped_high = builder
                    .build_select(gt_max, max_v, val, "unit_clamp_high")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unit clamp high", &e))?
                    .into_int_value();
                let lt_min = builder
                    .build_int_compare(inkwell::IntPredicate::SLT, clamped_high, min_v, "unit_lt_min")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unit lt min", &e))?;
                let clamped = builder
                    .build_select(lt_min, min_v, clamped_high, "unit_clamp")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unit clamp", &e))?
                    .into_int_value();
                vreg_map.insert(*dest, clamped.into());
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
                // DEFECT B (symmetric to the cranelift emit_box_int guard and to
                // UnboxInt's TAG_HEAP passthrough below): a value that is ALREADY a
                // tagged RuntimeValue heap handle (a user enum/struct/class =
                // TypeId >= 16, or ANY) must NOT be re-boxed — `handle << 3` shifts
                // its TAG_HEAP bits away and corrupts the pointer, so a later
                // rt_enum_payload/field access on the boxed value reads a garbage/nil
                // payload ("field access on nil receiver"). Pass such handles through
                // verbatim. A pure runtime tag-check cannot substitute here: a raw
                // int with nonzero low bits is indistinguishable from a tagged value,
                // so BoxInt must rely on the static source type.
                let src_ty = vreg_types.get(value).copied();
                if matches!(src_ty, Some(t) if t == crate::hir::TypeId::ANY || t.0 >= 16) {
                    let val = self.get_vreg(value, vreg_map)?;
                    vreg_map.insert(*dest, val);
                } else {
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
                let tag = builder
                    .build_and(int_val, i64_type.const_int(7, false), "unbox_tag")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox tag", &e))?;
                let is_int = builder
                    .build_int_compare(inkwell::IntPredicate::EQ, tag, i64_type.const_zero(), "unbox_is_int")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox int test", &e))?;
                let is_true = builder
                    .build_int_compare(
                        inkwell::IntPredicate::EQ,
                        int_val,
                        i64_type.const_int(11, false),
                        "unbox_is_true",
                    )
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox true test", &e))?;
                let is_false = builder
                    .build_int_compare(
                        inkwell::IntPredicate::EQ,
                        int_val,
                        i64_type.const_int(19, false),
                        "unbox_is_false",
                    )
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox false test", &e))?;
                let is_bool = builder
                    .build_or(is_true, is_false, "unbox_is_bool")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox bool test", &e))?;
                let raw_bool = builder
                    .build_int_z_extend(is_true, i64_type, "unbox_bool")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox bool", &e))?;
                let int_or_value = builder
                    .build_select(is_int, shifted, int_val, "unbox_int_or_value")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox integer", &e))?
                    .into_int_value();
                let unboxed = builder
                    .build_select(is_bool, raw_bool, int_or_value, "unbox_scalar")
                    .map_err(|e| crate::error::factory::llvm_build_failed("unbox scalar", &e))?;
                vreg_map.insert(*dest, unboxed);
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
                            let str_val = self.context_ref().const_string(s.as_bytes(), false);
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
                            // Interned: static fstring literal part re-executes
                            // per format evaluation (no-GC tier, see
                            // rt_string_new_literal).
                            let lit_new = module.get_function("rt_string_new_literal").unwrap_or_else(|| {
                                let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                                module.add_function("rt_string_new_literal", fn_type, None)
                            });
                            let call = builder
                                .build_call(lit_new, &[str_ptr_int.into(), str_len.into()], "lit_str")
                                .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new_literal", &e))?;
                            call.try_as_basic_value()
                                .left()
                                .unwrap_or_else(|| i64_type.const_int(0, false).into())
                        }
                        FStringPart::Expr(vreg) => {
                            let val = self.get_vreg(vreg, vreg_map)?;
                            // An untagged FloatValue (e.g. a typed f64 struct-field
                            // load, which MIR does not BoxFloat) must be TAGGED here,
                            // not bitcast: coerce_value_to_type bitcasts f64→i64 raw,
                            // making rt_value_to_string print the IEEE-754 bit
                            // pattern as an integer (1.0 → 4607182418800017408).
                            let coerced = if val.is_float_value() {
                                self.build_box_float_value(val, builder, module)?.into()
                            } else {
                                self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                            };
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
                            // Same float-tagging requirement as FStringPart::Expr above.
                            let coerced = if val.is_float_value() {
                                self.build_box_float_value(val, builder, module)?.into()
                            } else {
                                self.coerce_value_to_type(val, Some(i64_type.into()), builder)?
                            };
                            // Create format spec string constant
                            let spec_val = self.context_ref().const_string(format_spec.as_bytes(), false);
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

            // MethodCallVirtual — load object[0], then call the selected vtable slot.
            MirInst::MethodCallVirtual {
                dest,
                receiver,
                vtable_slot,
                param_types,
                return_type,
                args,
            } => {
                use inkwell::types::BasicType;

                let i64_type = self.runtime_int_type();
                let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                let receiver_value = self.get_vreg(receiver, vreg_map)?;
                let receiver_int = self.coerce_value_to_type(receiver_value, Some(i64_type.into()), builder)?;
                let receiver_int = receiver_int.into_int_value();
                let object_bits = builder
                    .build_and(receiver_int, i64_type.const_int(!0x7, false), "virtual_object_bits")
                    .map_err(|e| crate::error::factory::llvm_build_failed("mask virtual receiver", &e))?;
                let object_ptr = builder
                    .build_int_to_ptr(object_bits, ptr_type, "virtual_object")
                    .map_err(|e| crate::error::factory::llvm_build_failed("virtual object pointer", &e))?;
                let vtable_ptr = builder
                    .build_load(ptr_type, object_ptr, "vtable")
                    .map_err(|e| crate::error::factory::llvm_build_failed("load vtable", &e))?
                    .into_pointer_value();
                let slot_ptr = unsafe {
                    builder.build_gep(
                        ptr_type,
                        vtable_ptr,
                        &[self.context_ref().i32_type().const_int(*vtable_slot as u64, false)],
                        "vtable_slot",
                    )
                }
                .map_err(|e| crate::error::factory::llvm_build_failed("vtable slot", &e))?;
                let method_ptr = builder
                    .build_load(ptr_type, slot_ptr, "virtual_method")
                    .map_err(|e| crate::error::factory::llvm_build_failed("load virtual method", &e))?
                    .into_pointer_value();

                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = vec![receiver_int.into()];
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                    arg_vals.push(casted.into());
                }
                let mut llvm_params: Vec<inkwell::types::BasicMetadataTypeEnum> = vec![i64_type.into()];
                llvm_params.extend(
                    param_types
                        .iter()
                        .map(|_| inkwell::types::BasicMetadataTypeEnum::from(i64_type)),
                );
                let fn_type = if *return_type == crate::hir::TypeId::VOID {
                    self.context_ref().void_type().fn_type(&llvm_params, false)
                } else {
                    self.llvm_type(return_type)?.fn_type(&llvm_params, false)
                };
                let call = builder
                    .build_indirect_call(fn_type, method_ptr, &arg_vals, "virtual_call")
                    .map_err(|e| crate::error::factory::llvm_build_failed("virtual call", &e))?;
                if let Some(d) = dest {
                    let value = call
                        .try_as_basic_value()
                        .left()
                        .unwrap_or_else(|| i64_type.const_zero().into());
                    vreg_map.insert(*d, value);
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

                // Extract plain method name from qualified name. LLVM-side symbol
                // resolution may already have sanitized `Type.method` to
                // `Type_dot_method`, so handle both spellings here.
                let method = if let Some(dot_pos) = func_name.rfind("_dot_") {
                    &func_name[dot_pos + "_dot_".len()..]
                } else {
                    func_name.rsplit('.').next().unwrap_or(func_name)
                };

                // For qualified user-defined methods like `Boxed.get`, prefer
                // the exact resolved function symbol before consulting builtin
                // method shims such as `get -> rt_index_get`. Otherwise a
                // struct method can be misrouted through a collection helper
                // purely because it shares a common short name.
                let resolved_direct = self
                    .use_map
                    .get(func_name)
                    .or_else(|| self.import_map.get(func_name))
                    .map(|s| s.as_str());
                let dotted_direct = func_name.replace("_dot_", ".");
                let direct_func = resolved_direct
                    .and_then(|n| module.get_function(n))
                    .or_else(|| resolved_direct.and_then(|n| module.get_function(&n.replace("_dot_", "."))))
                    .or_else(|| module.get_function(func_name))
                    .or_else(|| module.get_function(&dotted_direct));
                if direct_func.is_some() && (func_name.contains('.') || func_name.contains("_dot_")) {
                    let mut all_args = vec![*receiver];
                    all_args.extend_from_slice(args);
                    let func = direct_func.unwrap();
                    let declared_param_types = func.get_type().get_param_types();
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    for (i, arg) in all_args.iter().enumerate() {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let target_ty = declared_param_types.get(i).copied().or_else(|| Some(i64_type.into()));
                        let casted = self.coerce_value_to_type(val, target_ty, builder)?;
                        arg_vals.push(casted.into());
                    }
                    let call_site = if declared_param_types.len() != arg_vals.len() {
                        let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                            arg_vals.iter().map(|_| i64_type.into()).collect();
                        let fn_type = i64_type.fn_type(&param_types, false);
                        let fn_ptr = func.as_global_value().as_pointer_value();
                        builder
                            .build_indirect_call(fn_type, fn_ptr, &arg_vals, "mcall_direct")
                            .map_err(|e| crate::error::factory::llvm_build_failed("qualified method call", &e))?
                    } else {
                        builder
                            .build_call(func, &arg_vals, "mcall_direct")
                            .map_err(|e| crate::error::factory::llvm_build_failed("qualified method call", &e))?
                    };
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        } else {
                            vreg_map.insert(*d, i64_type.const_int(0, false).into());
                        }
                    }
                    return Ok(());
                }

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
                    "to_u8" | "to_i8" | "to_u16" | "to_i16" | "to_u32" | "to_i32" | "to_u64" | "to_i64" | "to_int"
                ) {
                    let recv_val = self.get_vreg(receiver, vreg_map)?;
                    let int_type = match method {
                        "to_u8" | "to_i8" => self.context_ref().i8_type(),
                        "to_u16" | "to_i16" => self.context_ref().i16_type(),
                        "to_u32" | "to_i32" => self.context_ref().i32_type(),
                        _ => self.context_ref().i64_type(),
                    };
                    let converted = self.coerce_value_to_type(recv_val, Some(int_type.into()), builder)?;
                    if let Some(d) = dest {
                        vreg_map.insert(*d, converted);
                    }
                    return Ok(());
                }

                // FLOAT conversion builtins. `pipeline/native_project/mangle.rs`
                // deliberately leaves `to_f32`/`to_f64`/`to_float` BARE when the
                // receiver type was erased, on the documented contract that codegen
                // lowers them through builtin numeric conversion. Cranelift honours
                // that contract (`codegen/instr/methods.rs` numeric_cast_target), but
                // the LLVM arm above covered only the INTEGER targets -- so a bare
                // `to_f32` fell through to the suffix scan below and aborted with
                // "ambiguous LLVM method resolution" the moment a module declared
                // more than one `T.to_f32`. That asymmetry is why only the LLVM lane
                // was blocked. Semantics below mirror the cranelift table exactly.
                //
                // NOTE: `coerce_value_to_type` must NOT be used for the int->float
                // direction here: it BITCASTS i64 <-> f64 to preserve the tagged-value
                // ABI, which would reinterpret an integer's bits as a double instead
                // of converting its value.
                let float_cast_bits = match method {
                    "to_f32" => Some(32u32),
                    "to_f64" | "to_float" => Some(64u32),
                    _ => None,
                };
                if let Some(bits) = float_cast_bits {
                    use crate::hir::TypeId;
                    let recv_val = self.get_vreg(receiver, vreg_map)?;
                    let f32_ty = self.context_ref().f32_type();
                    let f64_ty = self.context_ref().f64_type();
                    let target_ty = if bits == 32 { f32_ty } else { f64_ty };
                    let from_ty = vreg_types.get(receiver).copied();
                    let converted: inkwell::values::BasicValueEnum<'static> = match recv_val {
                        inkwell::values::BasicValueEnum::FloatValue(fv) => {
                            let cur = fv.get_type();
                            if cur == target_ty {
                                fv.into()
                            } else if bits == 64 {
                                builder
                                    .build_float_ext(fv, f64_ty, "fpext")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("to_f64 fpext", &e))?
                                    .into()
                            } else {
                                builder
                                    .build_float_trunc(fv, f32_ty, "fptrunc")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("to_f32 fptrunc", &e))?
                                    .into()
                            }
                        }
                        inkwell::values::BasicValueEnum::IntValue(iv) => {
                            // A HIR-float receiver carried in the tagged i64 ABI must be
                            // REINTERPRETED, not numerically converted -- same rule
                            // `coerce_value_to_type` applies for i64 <-> f64.
                            let hir_float = matches!(from_ty, Some(TypeId::F32) | Some(TypeId::F64));
                            if hir_float && iv.get_type().get_bit_width() == 64 {
                                let as_f64 = builder
                                    .build_bit_cast(iv, f64_ty, "i2f")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("bitcast_i2f", &e))?
                                    .into_float_value();
                                if bits == 32 {
                                    builder
                                        .build_float_trunc(as_f64, f32_ty, "fptrunc")
                                        .map_err(|e| crate::error::factory::llvm_build_failed("to_f32 fptrunc", &e))?
                                        .into()
                                } else {
                                    as_f64.into()
                                }
                            } else {
                                let unsigned = matches!(
                                    from_ty,
                                    Some(TypeId::U8) | Some(TypeId::U16) | Some(TypeId::U32) | Some(TypeId::U64)
                                );
                                if unsigned {
                                    builder
                                        .build_unsigned_int_to_float(iv, target_ty, "uitofp")
                                        .map_err(|e| crate::error::factory::llvm_build_failed("uitofp", &e))?
                                        .into()
                                } else {
                                    builder
                                        .build_signed_int_to_float(iv, target_ty, "sitofp")
                                        .map_err(|e| crate::error::factory::llvm_build_failed("sitofp", &e))?
                                        .into()
                                }
                            }
                        }
                        other => self.coerce_value_to_type(other, Some(target_ty.into()), builder)?,
                    };
                    if let Some(d) = dest {
                        vreg_map.insert(*d, converted);
                    }
                    return Ok(());
                }

                if matches!(method, "chr" | "to_char") {
                    let recv_val = self.get_vreg(receiver, vreg_map)?;
                    let recv_casted = self.coerce_value_to_type(recv_val, Some(i64_type.into()), builder)?;
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    let rt_func = module
                        .get_function("char_from_code")
                        .unwrap_or_else(|| module.add_function("char_from_code", fn_type, None));
                    let call_site = builder
                        .build_call(rt_func, &[recv_casted.into()], "char_from_code")
                        .map_err(|e| crate::error::factory::llvm_build_failed("char_from_code call", &e))?;
                    if let Some(d) = dest {
                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*d, ret_val);
                        }
                    }
                    return Ok(());
                }

                if matches!(method, "min" | "max") && args.len() == 1 {
                    let lhs = self.get_vreg(receiver, vreg_map)?;
                    let rhs = self.get_vreg(&args[0], vreg_map)?;
                    let lhs = self.coerce_value_to_type(lhs, Some(i64_type.into()), builder)?;
                    let rhs = self.coerce_value_to_type(rhs, Some(i64_type.into()), builder)?;
                    let lhs = lhs.into_int_value();
                    let rhs = rhs.into_int_value();
                    let pred = if method == "min" {
                        inkwell::IntPredicate::SLE
                    } else {
                        inkwell::IntPredicate::SGE
                    };
                    let cmp = builder
                        .build_int_compare(pred, lhs, rhs, "int_minmax_cmp")
                        .map_err(|e| crate::error::factory::llvm_build_failed("int min/max compare", &e))?;
                    let selected = builder
                        .build_select(cmp, lhs, rhs, "int_minmax_select")
                        .map_err(|e| crate::error::factory::llvm_build_failed("int min/max select", &e))?;
                    if let Some(d) = dest {
                        vreg_map.insert(*d, selected);
                    }
                    return Ok(());
                }

                // Map well-known methods to runtime functions
                // MUST match Cranelift's exact mapping at src/codegen/instr/calls.rs:3162-3201
                let runtime_func = match method {
                    // Copied verbatim from Cranelift lines 3163-3200
                    "contains" | "contains_key" | "has_key" | "has" => Some("rt_contains"),
                    "len" | "length" => Some("rt_len"),
                    "starts_with" => Some("rt_string_starts_with"),
                    "ends_with" => Some("rt_string_ends_with"),
                    "concat" => Some("rt_string_concat"),
                    "char_at" => Some("rt_string_char_at"),
                    // Receiver-polymorphic; see emitter.rs. `at` on an array
                    // receiver must reach `rt_array_at` (a real `Option`), not
                    // the string-only `rt_string_char_at`, which answers `nil`
                    // for every index of every array. Cranelift already routes
                    // `at` to `rt_at` (codegen/instr/calls.rs); this keeps the
                    // two backends from disagreeing on the same source.
                    "at" => Some("rt_at"),
                    "char_code_at" => Some("rt_string_char_code_at"),
                    "byte_at" => Some("rt_string_byte_at"),
                    "push" => Some("rt_array_push"),
                    "pop" => Some("rt_array_pop"),
                    "clear" => Some("rt_array_clear"),
                    "join" => Some("rt_string_join"),
                    "trim" => Some("rt_string_trim"),
                    "trim_start" => Some("rt_string_trim_start"),
                    "trim_end" => Some("rt_string_trim_end"),
                    "split" => Some("rt_string_split"),
                    "bytes" => Some("rt_string_bytes"),
                    "chars" => Some("rt_string_chars"),
                    "replace" => Some("rt_string_replace"),
                    "to_upper" | "upper" => Some("rt_string_to_upper"),
                    "to_lower" | "lower" => Some("rt_string_to_lower"),
                    "to_int" | "to_i64" => Some("rt_string_to_int"),
                "parse_int" | "parse_i32" | "parse_i64" => Some("rt_string_parse_int"),
                    "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => {
                        Some("rt_string_to_float")
                    }
                    // Receiver-polymorphic: see the matching note in
                    // llvm/emitter.rs. Routing `index_of` to the string-only
                    // `rt_string_find` made every array `index_of` return the
                    // -1 receiver-mismatch sentinel under LLVM while the
                    // Cranelift/JIT path returned the true index.
                    "index_of" => Some("rt_index_of"),
                    "find" | "find_str" => Some("rt_string_find"),
                    "rfind" | "last_index_of" => Some("rt_string_rfind"),
                    "to_string" | "to_text" | "str" => Some("rt_to_string"),
                    "slice" | "substring" => Some("rt_slice"),
                    "get" => Some("rt_index_get"),
                    "keys" => Some("rt_dict_keys"),
                    "values" => Some("rt_dict_values"),
                    // Receiver-dispatched — see the matching arm in
                    // codegen/instr/closures_structs.rs. Name-keyed table with
                    // no receiver type, so `rt_dict_remove` here silently
                    // no-opped every array `.remove(i)` on the native lane too.
                    // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
                    "remove" => Some("rt_collection_remove"),
                    "filter" => Some("rt_array_filter"),
                    "sort" => Some("rt_array_sort"),
                    "reverse" => Some("rt_array_reverse"),
                    "first" => Some("rt_array_first"),
                    "last" => Some("rt_array_last"),
                    "find" => Some("rt_array_find"),
                    "any" => Some("rt_array_any"),
                    "all" => Some("rt_array_all"),
                    // LLVM-specific mappings (not in Cranelift, verified to exist)
                    "repeat" => Some("lib__common__string_core__str_repeat"),
                    "map" => Some("rt_option_map"),
                    // Option/Result methods (LLVM-specific)
                    "unwrap" | "unwrap_or" | "unwrap_err" => Some("rt_enum_payload"),
                    "is_none" => Some("rt_is_none"),
                    "is_some" => Some("rt_is_some"),
                    "is_ok" | "is_err" => Some("rt_enum_check_discriminant"),
                    _ => None,
                };

                if let Some(rt_name) = runtime_func {
                    if rt_name == "rt_len" {
                        let len_args = [*receiver];
                        if self.compile_inline_len(*dest, &len_args, vreg_map, builder, false)? {
                            return Ok(());
                        }
                    }
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
                    for (arg_idx, arg) in all_args_vregs.iter().enumerate() {
                        let mut val = self.get_vreg(arg, vreg_map)?;
                        // Membership needle must be boxed to match the tagged
                        // store; see build_wrap_membership_needle.
                        if rt_name == "rt_contains" && arg_idx == 1 {
                            val = self.build_wrap_membership_needle(*arg, val, vreg_types, builder, module)?;
                        }
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
                            | "rt_dict_contains"
                            | "rt_is_none"
                            | "rt_is_some"
                            | "rt_array_any"
                            | "rt_array_all"
                    );
                    let fn_type = if returns_bool {
                        self.context_ref().bool_type().fn_type(&param_types, false)
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
                        // The scan above keys on the LEAF NAME ONLY, so every symbol
                        // ending in `.<method>` collides regardless of its receiver
                        // type. Narrow by RECEIVER TYPE first, then by arity:
                        // `f64.to_f32` and `i64.to_f32` stop being ambiguous the
                        // moment the receiver's type is known.
                        //
                        // Narrowing never INVENTS a pick. A filter is applied only
                        // when it leaves exactly one candidate; if the receiver type
                        // is unknown, or still does not single one out, the ambiguity
                        // is reported exactly as before. Silently taking a first hit
                        // is the defect class this guard exists to catch.
                        if matches.len() > 1 {
                            if let Some(recv_name) =
                                vreg_types.get(receiver).copied().and_then(primitive_type_symbol_name)
                            {
                                let qualified = format!(".{}", recv_name);
                                let narrowed: Vec<_> = matches
                                    .iter()
                                    .filter(|(name, _)| match name.strip_suffix(&suffix) {
                                        Some(head) => head == recv_name || head.ends_with(&qualified),
                                        None => false,
                                    })
                                    .cloned()
                                    .collect();
                                if narrowed.len() == 1 {
                                    matches = narrowed;
                                }
                            }
                        }
                        if matches.len() > 1 {
                            let expected_params = 1 + args.len();
                            let narrowed: Vec<_> = matches
                                .iter()
                                .filter(|(_, f)| f.get_type().get_param_types().len() == expected_params)
                                .cloned()
                                .collect();
                            if narrowed.len() == 1 {
                                matches = narrowed;
                            }
                        }
                        // A SOLE suffix hit still carries no owner-type guarantee — the
                        // scan keys on the leaf name only. When the receiver's type is
                        // known and disagrees with the sole candidate's owner, reject it
                        // rather than binding blindly: `text.bytes()` had exactly one
                        // suffix match (`PointerSize.bytes`) and was bound unchecked,
                        // producing a wrong-callee SIGSEGV at Stage-3 self-host.
                        // doc/08_tracking/bug/stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md
                        if matches.len() == 1 {
                            if let Some(recv_name) =
                                vreg_types.get(receiver).copied().and_then(primitive_type_symbol_name)
                            {
                                let owner_ok = matches[0]
                                    .0
                                    .strip_suffix(&suffix)
                                    .is_some_and(|head| calls::suffix_owner_matches(head, recv_name));
                                if !owner_ok {
                                    matches.clear();
                                }
                            }
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

                    let fallback_name = resolved
                        .map(|n| n.replace("_dot_", "."))
                        .unwrap_or_else(|| dotted_name.clone());
                    let runtime_spec = crate::codegen::runtime_sffi::RUNTIME_FUNCS
                        .iter()
                        .find(|spec| spec.name == fallback_name || spec.name == func_name || spec.name == dotted_name);
                    let fallback_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = runtime_spec
                        .map(|spec| {
                            spec.params
                                .iter()
                                .map(|ty| {
                                    if *ty == cranelift_codegen::ir::types::I8 {
                                        self.context_ref().i8_type().into()
                                    } else if *ty == cranelift_codegen::ir::types::I32 {
                                        self.context_ref().i32_type().into()
                                    } else {
                                        i64_type.into()
                                    }
                                })
                                .collect()
                        })
                        .unwrap_or_else(|| all_args.iter().map(|_| i64_type.into()).collect());
                    let fallback_fn_type = if let Some(spec) = runtime_spec {
                        match spec.returns {
                            [] => self.context_ref().void_type().fn_type(&fallback_param_types, false),
                            [ret] if *ret == cranelift_codegen::ir::types::I8 => {
                                self.context_ref().i8_type().fn_type(&fallback_param_types, false)
                            }
                            [ret] if *ret == cranelift_codegen::ir::types::I32 => {
                                self.context_ref().i32_type().fn_type(&fallback_param_types, false)
                            }
                            _ => i64_type.fn_type(&fallback_param_types, false),
                        }
                    } else {
                        i64_type.fn_type(&fallback_param_types, false)
                    };
                    let func = if let Some(spec) = runtime_spec {
                        module
                            .get_function(spec.name)
                            .unwrap_or_else(|| module.add_function(spec.name, fallback_fn_type, None))
                    } else {
                        called_func.unwrap_or_else(|| module.add_function(&fallback_name, fallback_fn_type, None))
                    };
                    let declared_param_types = func.get_type().get_param_types();
                    let mut raw_arg_vals: Vec<inkwell::values::IntValue> = Vec::new();
                    for (i, arg) in all_args.iter().enumerate() {
                        let val = self.get_vreg(arg, vreg_map)?;
                        let target_ty = declared_param_types.get(i).copied().or_else(|| Some(i64_type.into()));
                        let casted = self.coerce_value_to_type(val, target_ty, builder)?;
                        raw_arg_vals.push(casted.into_int_value());
                    }
                    let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                    let runtime_name = runtime_spec.map(|spec| spec.name).unwrap_or(&fallback_name);
                    let boxed_indices = crate::codegen::instr::calls::boxed_text_arg_indices(runtime_name);
                    let text_indices = crate::codegen::instr::calls::process_c_runtime_arg_indices(runtime_name)
                        .map(|(indices, _)| indices)
                        .or_else(|| crate::codegen::instr::calls::text_arg_indices(runtime_name));
                    if let Some(boxed_indices) = boxed_indices {
                        let rt_string_data = module.get_function("rt_string_data").unwrap_or_else(|| module.add_function("rt_string_data", i64_type.fn_type(&[i64_type.into()], false), None));
                        let rt_string_len = module.get_function("rt_string_len").unwrap_or_else(|| module.add_function("rt_string_len", i64_type.fn_type(&[i64_type.into()], false), None));
                        let rt_string_new = module.get_function("rt_string_new").unwrap_or_else(|| module.add_function("rt_string_new", i64_type.fn_type(&[i64_type.into(), i64_type.into()], false), None));
                        for (i, val) in raw_arg_vals.iter().enumerate() {
                            if boxed_indices.contains(&i) {
                                let ptr = builder.build_call(rt_string_data, &[(*val).into()], "sffi_boxed_text_ptr").map_err(|e| crate::error::factory::llvm_build_failed("rt_string_data", &e))?.try_as_basic_value().left().unwrap();
                                let len = builder.build_call(rt_string_len, &[(*val).into()], "sffi_boxed_text_len").map_err(|e| crate::error::factory::llvm_build_failed("rt_string_len", &e))?.try_as_basic_value().left().unwrap();
                                let boxed = builder.build_call(rt_string_new, &[ptr.into(), len.into()], "sffi_boxed_text_value").map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?.try_as_basic_value().left().unwrap();
                                arg_vals.push(boxed.into());
                            } else {
                                arg_vals.push((*val).into());
                            }
                        }
                    } else if let Some(text_indices) = text_indices {
                        let rt_string_data = module.get_function("rt_string_data").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_string_data", fn_type, None)
                        });
                        let rt_string_len = module.get_function("rt_string_len").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_string_len", fn_type, None)
                        });
                        for (i, val) in raw_arg_vals.iter().enumerate() {
                            if text_indices.contains(&i) {
                                let ptr = builder
                                    .build_call(rt_string_data, &[(*val).into()], "sffi_text_ptr")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_data", &e))?
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap_or_else(|| i64_type.const_int(0, false).into());
                                let len = builder
                                    .build_call(rt_string_len, &[(*val).into()], "sffi_text_len")
                                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_len", &e))?
                                    .try_as_basic_value()
                                    .left()
                                    .unwrap_or_else(|| i64_type.const_int(0, false).into());
                                arg_vals.push(ptr.into());
                                arg_vals.push(len.into());
                            } else {
                                arg_vals.push((*val).into());
                            }
                        }
                    } else {
                        arg_vals.extend(
                            raw_arg_vals
                                .iter()
                                .map(|v| inkwell::values::BasicMetadataValueEnum::from(*v)),
                        );
                    }
                    let declared_params = func.get_type().get_param_types().len();
                    let call_site = if declared_params != arg_vals.len() {
                        let fn_ptr = func.as_global_value().as_pointer_value();
                        builder
                            .build_indirect_call(fallback_fn_type, fn_ptr, &arg_vals, "mcall")
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
                    | ("Dict" | "dict", "contains")
                    | ("String" | "string", "has")
                    | ("Array" | "array", "has")
                    | ("Dict" | "dict", "has") => Some("rt_contains"),
                    ("String" | "string", "substring") => Some("rt_slice"),
                    ("String" | "string", "split") => Some("rt_string_split"),
                    ("String" | "string" | "str" | "text", "trim") => Some("rt_string_trim"),
                    ("String" | "string" | "str" | "text", "trim_start") => Some("rt_string_trim_start"),
                    ("String" | "string" | "str" | "text", "trim_end") => Some("rt_string_trim_end"),
                    ("String" | "string", "replace") => Some("rt_string_replace"),
                    ("String" | "string" | "str" | "text", "find" | "find_str" | "index_of") => Some("rt_string_find"),
                    ("String" | "string", "to_upper") | ("String" | "string", "upper") => Some("rt_string_to_upper"),
                    ("String" | "string", "to_lower") | ("String" | "string", "lower") => Some("rt_string_to_lower"),
                    ("String" | "string", "char_at") => Some("rt_string_char_at"),
                    ("String" | "string", "char_code_at") => Some("rt_string_char_code_at"),
                    ("String" | "string", "byte_at") => Some("rt_string_byte_at"),
                    ("Dict" | "dict", "get") => Some("rt_index_get"),
                    ("Dict" | "dict", "set") => Some("rt_dict_set"),
                    ("Dict" | "dict", "len") => Some("rt_dict_len"),
                    ("Dict" | "dict", "clear") => Some("rt_dict_clear"),
                    ("Dict" | "dict", "keys") => Some("rt_dict_keys"),
                    ("Dict" | "dict", "values") => Some("rt_dict_values"),
                    // `rt_dict_contains` is the exported name in BOTH runtimes
                    // (Rust: `rt_dict_contains(dict, key) -> bool`; C:
                    // `int8_t rt_dict_contains(int64_t, int64_t)`). This used to
                    // map to `rt_dict_contains_key`, which is defined in neither,
                    // so `d.contains_key(k)` failed at link time under the LLVM
                    // backend.
                    ("Dict" | "dict", "contains_key") => Some("rt_dict_contains"),
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
                if let Some(global) = module.get_global(global_name) {
                    let loaded = builder
                        .build_load(i64_type, global.as_pointer_value(), "gload")
                        .map_err(|e| crate::error::factory::llvm_build_failed("global load", &e))?;
                    vreg_map.insert(*dest, loaded);
                } else {
                    let resolved_name = self
                        .use_map
                        .get(global_name.as_str())
                        .or_else(|| self.import_map.get(global_name.as_str()))
                        .map(|s| s.as_str())
                        .unwrap_or(global_name.as_str());
                    let resolved_dotted = resolved_name.replace("_dot_", ".");
                    let func = module
                        .get_function(resolved_name)
                        .or_else(|| module.get_function(&resolved_dotted))
                        .or_else(|| module.get_function(global_name));

                    if let Some(func) = func {
                        let alloc_fn_type = i64_type.fn_type(&[i64_type.into()], false);
                        let alloc_fn = module
                            .get_function("rt_alloc")
                            .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
                        let closure_size = i64_type.const_int(16, false);
                        let alloc_call = builder
                            .build_call(alloc_fn, &[closure_size.into()], "alloc_closure")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_alloc", &e))?;
                        let closure_i64 = alloc_call
                            .try_as_basic_value()
                            .left()
                            .ok_or_else(|| CompileError::semantic("rt_alloc did not return closure storage"))?;
                        let closure_ptr = builder
                            .build_int_to_ptr(
                                closure_i64.into_int_value(),
                                self.context_ref().ptr_type(inkwell::AddressSpace::default()),
                                "closure_ptr",
                            )
                            .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?;
                        let fn_addr = builder
                            .build_ptr_to_int(func.as_global_value().as_pointer_value(), i64_type, "fn_addr")
                            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
                        let direct_marker = i64_type.const_int(0x5344_4952_4543_5446, false);
                        let slot_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                        let fn_slot = builder
                            .build_pointer_cast(closure_ptr, slot_ptr_type, "fn_slot")
                            .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn slot", &e))?;
                        builder
                            .build_store(fn_slot, fn_addr)
                            .map_err(|e| crate::error::factory::llvm_build_failed("store fn addr", &e))?;
                        let marker_ptr = unsafe {
                            builder.build_gep(
                                self.context_ref().i8_type(),
                                closure_ptr,
                                &[self.context_ref().i32_type().const_int(8, false)],
                                "closure_marker_ptr",
                            )
                        }
                        .map_err(|e| crate::error::factory::llvm_build_failed("gep marker", &e))?;
                        let marker_slot = builder
                            .build_pointer_cast(marker_ptr, slot_ptr_type, "marker_slot")
                            .map_err(|e| crate::error::factory::llvm_cast_failed("cast marker slot", &e))?;
                        builder
                            .build_store(marker_slot, direct_marker)
                            .map_err(|e| crate::error::factory::llvm_build_failed("store marker", &e))?;
                        vreg_map.insert(*dest, closure_i64);
                    } else {
                        return Err(CompileError::semantic(format!(
                            "llvm global load referenced undeclared symbol `{}`",
                            global_name
                        )));
                    }
                }
            }
            MirInst::GlobalStore { global_name, value, ty } => {
                let i64_type = self.runtime_int_type();
                let val = self.get_vreg(value, vreg_map)?;
                let coerced = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                let global = module.get_global(global_name).ok_or_else(|| {
                    CompileError::semantic(format!(
                        "llvm global store referenced undeclared symbol `{}`",
                        global_name
                    ))
                })?;
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

    #[cfg(feature = "llvm")]
    fn compile_emitter_simd_instruction(
        &self,
        inst: &crate::mir::MirInst,
        vreg_map: &mut VRegMap,
        local_allocas: &std::collections::HashMap<usize, inkwell::values::PointerValue<'static>>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let mut emitter = super::emitter::LlvmEmitter {
            backend: self,
            vreg_map,
            local_allocas,
            builder,
            module,
        };
        crate::codegen::dispatch::dispatch_instruction(&mut emitter, inst)
            .map_err(|e| crate::error::factory::llvm_build_failed("simd_dispatch", &e))
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
    use crate::codegen::backend_trait::NativeBackend;
    use crate::mir::{CallTarget, LocalKind, MirInst, MirLocal, Terminator, VReg};
    use simple_common::target::{Target, TargetArch, TargetOS};
    use std::collections::HashMap;

    #[test]
    fn virtual_call_uses_emitted_vtable_and_object_header() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let mut backend = LlvmBackend::new(target).unwrap();
        let symbol = "__vtable__Owner__for__Trait";

        let mut method = MirFunction::new(
            "Owner_dot_method".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        method.params.push(MirLocal {
            name: "self".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        method.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(1),
            value: 7,
        });
        method.blocks[0].terminator = Terminator::Return(Some(VReg(1)));

        let mut caller = MirFunction::new(
            "call_virtual".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        caller.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 3,
        });
        caller.blocks[0].instructions.push(MirInst::StructInit {
            dest: VReg(1),
            type_id: crate::hir::TypeId::I64,
            struct_name: Some("Owner".to_string()),
            vtable_symbol: Some(symbol.to_string()),
            struct_size: 8,
            field_offsets: vec![0],
            field_types: vec![crate::hir::TypeId::I64],
            field_values: vec![VReg(0)],
        });
        caller.blocks[0].instructions.push(MirInst::MethodCallVirtual {
            dest: Some(VReg(2)),
            receiver: VReg(1),
            vtable_slot: 0,
            param_types: vec![],
            return_type: crate::hir::TypeId::I64,
            args: vec![],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(VReg(2)));

        let mut mir = crate::mir::MirModule::new();
        mir.name = Some("virtual_dispatch".to_string());
        mir.functions = vec![method, caller];
        mir.vtable_impls.push((
            crate::hir::TypeId::I64,
            "Owner".to_string(),
            symbol.to_string(),
            vec![Some("Owner.method".to_string())],
            true,
        ));

        backend.compile(&mir).unwrap();
        let ir = backend.get_ir().unwrap();
        assert!(ir.contains(symbol), "{ir}");
        assert!(ir.contains("virtual_call"), "{ir}");
        assert!(ir.contains("i64 16"), "{ir}");
        backend.verify().unwrap();
    }

    #[test]
    fn method_call_static_arity_mismatch_uses_typed_indirect_call() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("method_arity_mismatch").unwrap();

        let mut method = MirFunction::new(
            "Boxed.read".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        method.blocks[0].instructions.push(MirInst::LocalAddr {
            dest: VReg(0),
            local_index: 1,
        });
        method.blocks[0].instructions.push(MirInst::Load {
            dest: VReg(1),
            addr: VReg(0),
            ty: crate::hir::TypeId::I64,
        });
        method.blocks[0].terminator = Terminator::Return(Some(VReg(1)));

        let mut caller = MirFunction::new(
            "main".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        caller.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 3,
        });
        caller.blocks[0].instructions.push(MirInst::MethodCallStatic {
            dest: Some(VReg(1)),
            receiver: VReg(0),
            func_name: "Boxed.read".to_string(),
            args: vec![],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(VReg(1)));

        backend.compile_function(&method).unwrap();
        backend.compile_function(&caller).unwrap();

        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("mcall_direct"), "{ir}");
        backend.verify().unwrap();
    }

    #[test]
    fn direct_string_calls_use_runtime_symbols() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("direct_string_runtime_redirects").unwrap();

        let mut func = MirFunction::new(
            "probe".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        for (dest, value) in [(VReg(0), 0), (VReg(1), 1), (VReg(2), 2)] {
            func.blocks[0].instructions.push(MirInst::ConstInt { dest, value });
        }
        for (dest, name, args) in [
            (VReg(3), "substring", vec![VReg(0), VReg(1), VReg(2)]),
            (VReg(4), "str.bytes", vec![VReg(0)]),
            (VReg(5), "str.chars", vec![VReg(0)]),
            (VReg(6), "str.ord", vec![VReg(0)]),
            (VReg(7), "rt_string_contains", vec![VReg(0), VReg(0)]),
            (VReg(8), "rt_dict_insert", vec![VReg(0), VReg(1), VReg(2)]),
            (VReg(9), "has", vec![VReg(0), VReg(1)]),
        ] {
            func.blocks[0].instructions.push(MirInst::Call {
                dest: Some(dest),
                target: CallTarget::from_name(name),
                args,
            });
        }
        func.blocks[0].terminator = Terminator::Return(Some(VReg(3)));

        backend.compile_function(&func).unwrap();
        let ir = backend.get_ir().unwrap();
        for symbol in [
            "@rt_slice",
            "@rt_string_bytes",
            "@rt_string_chars",
            "@rt_string_char_code_at",
            "@rt_contains",
            "@rt_dict_set",
            "@has(",
        ] {
            assert!(ir.contains(symbol), "missing {symbol}:\n{ir}");
        }
        for raw in [
            "@substring(",
            "str.bytes",
            "str.chars",
            "str.ord",
            "rt_string_contains",
            "@rt_dict_insert",
        ] {
            assert!(!ir.contains(raw), "raw call {raw} leaked:\n{ir}");
        }
        backend.verify().unwrap();
    }

    #[test]
    fn rt_value_bool_calls_receive_raw_boolean_bits() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("rt_value_bool_raw_bits").unwrap();

        let mut func = MirFunction::new(
            "probe".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        for (bool_reg, call_reg, value) in [(VReg(0), VReg(1), false), (VReg(2), VReg(3), true)] {
            func.blocks[0]
                .instructions
                .push(MirInst::ConstBool { dest: bool_reg, value });
            func.blocks[0].instructions.push(MirInst::Call {
                dest: Some(call_reg),
                target: CallTarget::from_name("rt_value_bool"),
                args: vec![bool_reg],
            });
        }
        func.blocks[0].terminator = Terminator::Return(Some(VReg(3)));

        backend.compile_function(&func).unwrap();
        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("call i64 @rt_value_bool(i64 0)"), "{ir}");
        assert!(ir.contains("call i64 @rt_value_bool(i64 1)"), "{ir}");
        assert!(!ir.contains("call i64 @rt_value_bool(i64 19)"), "{ir}");
        assert!(!ir.contains("call i64 @rt_value_bool(i64 11)"), "{ir}");
        backend.verify().unwrap();
    }

    #[test]
    fn process_run_uses_ptr_len_array_runtime_abi() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("process_run_runtime_abi").unwrap();

        let mut func = MirFunction::new(
            "probe".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        func.blocks[0].instructions.push(MirInst::ConstString {
            dest: VReg(0),
            value: "/bin/true".to_string(),
        });
        func.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(1),
            value: 1,
        });
        func.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(2)),
            target: CallTarget::from_name("rt_process_run"),
            args: vec![VReg(0), VReg(1)],
        });
        func.blocks[0].instructions.push(MirInst::MethodCallStatic {
            dest: Some(VReg(3)),
            receiver: VReg(0),
            func_name: "rt_process_run".to_string(),
            args: vec![VReg(1)],
        });
        func.blocks[0].terminator = Terminator::Return(Some(VReg(3)));

        backend.compile_function(&func).unwrap();
        let ir = backend.get_ir().unwrap();
        let calls: Vec<_> = ir
            .lines()
            .filter(|line| line.contains("call i64 @rt_process_run("))
            .collect();
        assert_eq!(calls.len(), 2, "{ir}");
        for call in calls {
            let call_args = call
                .split_once('(')
                .and_then(|(_, args)| args.rsplit_once(')'))
                .map(|(args, _)| args)
                .expect("malformed rt_process_run call");
            assert_eq!(call_args.matches("i64 ").count(), 3, "{call}\n{ir}");
        }
        assert!(ir.contains("call i64 @rt_string_data("), "{ir}");
        assert!(ir.contains("call i64 @rt_string_len("), "{ir}");
        assert!(!ir.contains("process_args_raw_ptr"), "{ir}");
        backend.verify().unwrap();
    }

    #[test]
    fn static_dict_remove_uses_runtime_symbol() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("static_builtin_runtime_redirects").unwrap();

        let mut func = MirFunction::new(
            "probe".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        for (dest, value) in [(VReg(0), 3), (VReg(1), 11)] {
            func.blocks[0].instructions.push(MirInst::ConstInt { dest, value });
        }
        func.blocks[0].instructions.push(MirInst::MethodCallStatic {
            dest: Some(VReg(2)),
            receiver: VReg(0),
            func_name: "Dict.remove".to_string(),
            args: vec![VReg(1)],
        });
        func.blocks[0].terminator = Terminator::Return(Some(VReg(2)));

        backend.compile_function(&func).unwrap();
        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("@rt_dict_remove"), "missing runtime remove:\n{ir}");
        assert!(!ir.contains("Dict.remove"), "raw Dict.remove leaked:\n{ir}");
        backend.verify().unwrap();
    }

    #[test]
    fn direct_call_dest_uses_callee_return_type() {
        let mut func = MirFunction::new(
            "caller".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Private,
        );
        func.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(0)),
            target: CallTarget::from_name("callee"),
            args: vec![],
        });

        let mut returns = HashMap::new();
        returns.insert("callee".to_string(), crate::hir::TypeId::I64);

        let types = build_vreg_types(&func, &returns);
        assert_eq!(types.get(&VReg(0)).copied(), Some(crate::hir::TypeId::I64));
    }

    #[test]
    fn rv32_call_return_scalar_compare_uses_native_compare() {
        let target = Target::new(TargetArch::Riscv32, TargetOS::SimpleOS);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("rv32_call_return_compare").unwrap();

        {
            let module_ref = backend.module.borrow();
            let module = module_ref.as_ref().unwrap();
            let rv_type = backend.runtime_int_type();
            let callee_type = rv_type.fn_type(&[], false);
            let callee = module.add_function("callee", callee_type, None);
            let builder_ref = backend.builder.borrow();
            let builder = builder_ref.as_ref().unwrap();
            let entry = backend.context_ref().append_basic_block(callee, "entry");
            builder.position_at_end(entry);
            builder.build_return(Some(&rv_type.const_int(1, false))).unwrap();
        }

        backend
            .function_return_types
            .borrow_mut()
            .insert("callee".to_string(), crate::hir::TypeId::I64);

        let mut func = MirFunction::new(
            "caller".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Private,
        );
        func.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(0)),
            target: CallTarget::from_name("callee"),
            args: vec![],
        });
        func.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(1),
            value: 1,
        });
        func.blocks[0].instructions.push(MirInst::BinOp {
            dest: VReg(2),
            op: crate::hir::BinOp::NotEq,
            left: VReg(0),
            right: VReg(1),
        });
        func.blocks[0].terminator = Terminator::Return(Some(VReg(2)));

        backend.compile_function(&func).unwrap();

        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("call i32 @callee()"));
        assert!(ir.contains("icmp ne i32"));
        assert!(!ir.contains("rt_native_neq"));
        backend.verify().unwrap();
    }

    #[test]
    fn rv32_param_guard_branch_uses_runtime_parameter() {
        let target = Target::new(TargetArch::Riscv32, TargetOS::SimpleOS);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("rv32_param_guard_branch").unwrap();

        let mut func = MirFunction::new(
            "heap_init_shape".to_string(),
            crate::hir::TypeId::BOOL,
            simple_parser::ast::Visibility::Private,
        );
        func.params.push(MirLocal {
            name: "heap_start".to_string(),
            ty: crate::hir::TypeId::U64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        func.params.push(MirLocal {
            name: "heap_size".to_string(),
            ty: crate::hir::TypeId::U64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        let fail = func.new_block();
        let ok = func.new_block();
        func.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(2),
            value: 8,
        });
        func.blocks[0].instructions.push(MirInst::BinOp {
            dest: VReg(3),
            op: crate::hir::BinOp::Lt,
            left: VReg(1),
            right: VReg(2),
        });
        func.blocks[0].terminator = Terminator::Branch {
            cond: VReg(3),
            then_block: fail,
            else_block: ok,
        };
        func.block_mut(fail).unwrap().instructions.push(MirInst::ConstBool {
            dest: VReg(4),
            value: false,
        });
        func.block_mut(fail).unwrap().terminator = Terminator::Return(Some(VReg(4)));
        func.block_mut(ok).unwrap().instructions.push(MirInst::ConstBool {
            dest: VReg(5),
            value: true,
        });
        func.block_mut(ok).unwrap().terminator = Terminator::Return(Some(VReg(5)));

        backend.compile_function(&func).unwrap();

        let ir = backend.get_ir().unwrap();
        assert!(ir.contains("define i32 @heap_init_shape(i32 %0, i32 %1)"));
        assert!(ir.contains("icmp slt i32"));
        assert!(ir.contains("br i1"));
        backend.verify().unwrap();
    }

    /// REPLACED 2026-08-01. The previous body of this test asserted
    /// `call i32 @rt_box_float(double` and `call double @rt_unbox_float(i32` —
    /// i.e. it PINNED a defect: neither `rt_box_float` nor `rt_unbox_float` is
    /// defined in either runtime (no `pub extern "C" fn` under
    /// src/compiler_rust/runtime, no definition in src/runtime/runtime_native.c),
    /// so on every 32-bit target the LLVM backend emitted calls to symbols that
    /// do not exist. The assertions were not relaxed — they were replaced with
    /// assertions naming the helpers that DO exist in both runtimes, plus
    /// explicit negative assertions so the dead names can never come back.
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
            let fn_type = backend.context_ref().void_type().fn_type(&[], false);
            let func = module.add_function("test", fn_type, None);
            let block = backend.context_ref().append_basic_block(func, "entry");
            builder.position_at_end(block);

            let float_val = backend.context_ref().f64_type().const_float(1.5);
            let boxed = backend
                .build_box_float_value(float_val.into(), builder, module)
                .unwrap();
            let unboxed = backend.build_unbox_float_value(boxed.into(), builder, module).unwrap();
            let _ = unboxed;
            builder.build_return(None).unwrap();
        }

        let ir = backend.get_ir().unwrap();
        // Positive artifacts: the 32-bit boxing path must call the helpers that
        // are actually EXPORTED by the runtimes.
        assert!(
            ir.contains("call i32 @rt_value_float(double"),
            "32-bit float boxing must call rt_value_float; IR was:\n{}",
            ir
        );
        assert!(
            ir.contains("call double @rt_value_as_float(i32"),
            "32-bit float unboxing must call rt_value_as_float; IR was:\n{}",
            ir
        );
        // Negative artifacts: these two symbols do not exist in ANY runtime.
        // Emitting them is what this test previously asserted.
        assert!(!ir.contains("rt_box_float"), "rt_box_float does not exist in any runtime");
        assert!(!ir.contains("rt_unbox_float"), "rt_unbox_float does not exist in any runtime");
        assert!(!ir.contains("bitcast i32"));
        backend.verify().unwrap();
    }

    /// True-positive control for the test above: on a 64-bit target the float
    /// boxing path is INLINE (shift/or + bitcast) and must emit no runtime call
    /// at all. Without this control, "no rt_box_float in the IR" could be
    /// satisfied by the boxing path going silent rather than by it being fixed.
    #[test]
    fn test_x86_64_float_boxing_is_inline_not_a_runtime_call() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("x64_float_boxing").unwrap();

        {
            let module_ref = backend.module.borrow();
            let module = module_ref.as_ref().unwrap();
            let builder_ref = backend.builder.borrow();
            let builder = builder_ref.as_ref().unwrap();
            let fn_type = backend.context_ref().void_type().fn_type(&[], false);
            let func = module.add_function("test", fn_type, None);
            let block = backend.context_ref().append_basic_block(func, "entry");
            builder.position_at_end(block);

            let float_val = backend.context_ref().f64_type().const_float(1.5);
            let boxed = backend
                .build_box_float_value(float_val.into(), builder, module)
                .unwrap();
            let unboxed = backend.build_unbox_float_value(boxed.into(), builder, module).unwrap();
            let _ = unboxed;
            builder.build_return(None).unwrap();
        }

        let ir = backend.get_ir().unwrap();
        assert!(!ir.contains("rt_value_float"), "64-bit boxing must stay inline");
        assert!(!ir.contains("rt_box_float"));
        assert!(!ir.contains("rt_unbox_float"));
        backend.verify().unwrap();
    }

    /// Regression guard for the `Dict.contains_key` runtime callee.
    ///
    /// This mapping is on the LIVE LLVM production path (unlike the emitter.rs
    /// probe emissions, which only `Vec*` SIMD instructions ever reach). It
    /// used to map to `rt_dict_contains_key`, which is defined in NEITHER
    /// runtime, so `d.contains_key(k)` compiled fine and then failed at LINK
    /// with `undefined reference to 'rt_dict_contains_key'`.
    ///
    /// `rt_dict_contains` is exported by BOTH runtimes — Rust
    /// `rt_dict_contains(dict, key) -> bool` and C
    /// `int8_t rt_dict_contains(int64_t, int64_t)` — confirmed with
    /// `nm --defined-only` on both built archives and then at the link level
    /// (broken name: rc=1 undefined reference; real name: rc=0 plus an ELF
    /// executable with the symbol at a real address).
    ///
    /// The positive assertions are the TRUE-POSITIVE CONTROL: deleting the
    /// mapping entirely would satisfy the negative assertion alone.
    #[test]
    fn dict_contains_key_maps_to_a_runtime_symbol_that_exists() {
        // Search the backend code only, never this test module, or the
        // assertions would match their own text and prove nothing.
        let src = include_str!("functions.rs");
        let split = src.find("#[cfg(all(test, feature = \"llvm\"))]").expect("test module marker");
        let code = &src[..split];

        assert!(
            !code.contains("\"rt_dict_contains_key\""),
            "rt_dict_contains_key is defined in neither runtime; emitting it \
             makes every Dict.contains_key call fail at link time"
        );
        assert!(
            code.contains("(\"Dict\" | \"dict\", \"contains_key\") => Some(\"rt_dict_contains\")"),
            "the Dict.contains_key mapping must still exist and must name \
             rt_dict_contains, the symbol both runtimes export"
        );
        // It returns a bool, so it must stay in the bool-returning list or the
        // declared LLVM prototype will disagree with the runtime.
        assert!(
            code.contains("| \"rt_dict_contains\""),
            "rt_dict_contains returns bool and must remain in the returns_bool set"
        );
    }

    /// Regression: a bare `bytes` leaf on a text receiver must reach
    /// `rt_string_bytes`, and must NEVER be suffix-matched onto an unrelated
    /// `*.bytes` user accessor.
    ///
    /// doc/08_tracking/bug/stage3_selfhost_segv_bare_leaf_bytes_hijacked_to_pointersize_bytes_2026-08-09.md
    /// The hijack bound `s.bytes()` to `lib__common__target__PointerSize.bytes`,
    /// a zero-content accessor returning the constant 8; the result was then
    /// used as a pointer, faulting at `si_addr 0x10` in Stage 3.
    #[test]
    fn bare_bytes_leaf_never_binds_to_unrelated_owner_bytes() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("bare_leaf_bytes_hijack").unwrap();

        // The decoy: same leaf, same arity (1 = receiver), unrelated owner.
        let mut decoy = MirFunction::new(
            "lib__common__target__PointerSize.bytes".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        decoy.params.push(MirLocal {
            name: "self".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        decoy.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 8,
        });
        decoy.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut caller = MirFunction::new(
            "hm_hash_text".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        caller.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 0,
        });
        caller.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(1)),
            target: CallTarget::from_name("bytes"),
            args: vec![VReg(0)],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(VReg(1)));

        backend.compile_function(&decoy).unwrap();
        backend.compile_function(&caller).unwrap();
        let ir = backend.get_ir().unwrap();

        assert!(ir.contains("@rt_string_bytes"), "{ir}");
        assert!(
            !ir.contains("call i64 @\"lib__common__target__PointerSize.bytes\""),
            "bare `bytes` was hijacked onto an unrelated owner: {ir}"
        );
        backend.verify().unwrap();
    }

    /// Regression: a bare leaf whose arity disagrees with a same-named free
    /// function must not silently bind to it. `T.max()` (0 args + receiver)
    /// against the free `fn max(a, b)` is the measured shape.
    #[test]
    fn bare_leaf_does_not_bind_free_function_with_wrong_arity() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        backend.create_module("bare_leaf_arity_guard").unwrap();

        let mut free_max = MirFunction::new(
            "max".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        for name in ["a", "b"] {
            free_max.params.push(MirLocal {
                name: name.to_string(),
                ty: crate::hir::TypeId::I64,
                kind: LocalKind::Parameter,
                is_ghost: false,
            });
        }
        free_max.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 1,
        });
        free_max.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        // A `Table.max` method exists, which is what makes the bare `max`
        // recognisably a method leaf rather than a call of the free function.
        let mut owner_max = MirFunction::new(
            "Table.max".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        owner_max.params.push(MirLocal {
            name: "self".to_string(),
            ty: crate::hir::TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        owner_max.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 2,
        });
        owner_max.blocks[0].terminator = Terminator::Return(Some(VReg(0)));

        let mut caller = MirFunction::new(
            "probe_max".to_string(),
            crate::hir::TypeId::I64,
            simple_parser::ast::Visibility::Public,
        );
        caller.blocks[0].instructions.push(MirInst::ConstInt {
            dest: VReg(0),
            value: 0,
        });
        caller.blocks[0].instructions.push(MirInst::Call {
            dest: Some(VReg(1)),
            target: CallTarget::from_name("max"),
            args: vec![VReg(0)],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(VReg(1)));

        backend.compile_function(&free_max).unwrap();
        backend.compile_function(&owner_max).unwrap();
        backend.compile_function(&caller).unwrap();
        let ir = backend.get_ir().unwrap();

        assert!(
            !ir.contains("call i64 @max(i64"),
            "1-arg bare `max` bound to the 2-param free function: {ir}"
        );
        backend.verify().unwrap();
    }

    #[test]
    fn suffix_owner_matches_only_the_receiver_type() {
        use super::calls::suffix_owner_matches;
        assert!(suffix_owner_matches("text", "string"));
        assert!(suffix_owner_matches("string", "string"));
        assert!(suffix_owner_matches("lib__common__text", "string"));
        assert!(!suffix_owner_matches("lib__common__target__PointerSize", "string"));
        assert!(!suffix_owner_matches("Vec4f", "f64"));
        assert!(suffix_owner_matches("f64", "f64"));
    }
}
