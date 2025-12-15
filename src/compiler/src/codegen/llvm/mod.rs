/// LLVM backend for 32-bit and 64-bit target support
///
/// This backend complements Cranelift by providing:
/// - 32-bit architecture support (i686, armv7, riscv32)
/// - Alternative 64-bit backend option
/// - Shared MIR transforms and runtime FFI specs
///
/// Requires the `llvm` feature flag and LLVM 18 toolchain to be enabled.

mod types;
pub use types::{BinOp, LlvmType};

use crate::codegen::backend_trait::NativeBackend;
use crate::error::CompileError;
use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};
use simple_common::target::Target;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::context::Context;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target as LlvmTarget, TargetMachine,
};
#[cfg(feature = "llvm")]
use inkwell::types::{BasicTypeEnum, FloatType, IntType};
#[cfg(feature = "llvm")]
use inkwell::values::FunctionValue;
#[cfg(feature = "llvm")]
use inkwell::IntPredicate;
#[cfg(feature = "llvm")]
use inkwell::OptimizationLevel;
#[cfg(feature = "llvm")]
use std::cell::RefCell;

/// LLVM-based code generator
pub struct LlvmBackend {
    target: Target,
    #[cfg(feature = "llvm")]
    context: Context,
    #[cfg(feature = "llvm")]
    module: RefCell<Option<Module<'static>>>,
    #[cfg(feature = "llvm")]
    builder: RefCell<Option<Builder<'static>>>,
}

// Manual Debug implementation since Context/Module/Builder don't implement Debug
impl std::fmt::Debug for LlvmBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LlvmBackend")
            .field("target", &self.target)
            .field("has_module", &cfg!(feature = "llvm"))
            .finish()
    }
}

// Continue with rest of original llvm.rs implementation
// (All other methods remain in this file for now to minimize changes)

impl LlvmBackend {
    /// Create a new LLVM backend for the given target
    pub fn new(target: Target) -> Result<Self, CompileError> {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = target; // Suppress unused warning when feature disabled
            return Err(CompileError::Semantic(
                "LLVM backend requires 'llvm' feature flag. \
                 Build with: cargo build --features llvm"
                    .to_string(),
            ));
        }

        #[cfg(feature = "llvm")]
        {
            Ok(Self {
                target,
                context: Context::create(),
                module: RefCell::new(None),
                builder: RefCell::new(None),
            })
        }
    }

    /// Get the target for this backend
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Get the LLVM target triple string for this target
    pub fn get_target_triple(&self) -> String {
        use simple_common::target::{TargetArch, TargetOS};

        let arch_str = match self.target.arch {
            TargetArch::X86_64 => "x86_64",
            TargetArch::Aarch64 => "aarch64",
            TargetArch::X86 => "i686",
            TargetArch::Arm => "armv7",
            TargetArch::Riscv64 => "riscv64",
            TargetArch::Riscv32 => "riscv32",
        };

        let os_str = match self.target.os {
            TargetOS::Linux => "unknown-linux-gnu",
            TargetOS::MacOS => "apple-darwin",
            TargetOS::Windows => "pc-windows-msvc",
            TargetOS::FreeBSD => "unknown-freebsd",
            TargetOS::Any | TargetOS::None => "unknown-unknown",
        };

        format!("{}-{}", arch_str, os_str)
    }

    /// Get pointer width (32 or 64 bits)
    pub fn pointer_width(&self) -> u32 {
        use simple_common::target::TargetArch;
        match self.target.arch {
            TargetArch::X86 | TargetArch::Arm | TargetArch::Riscv32 => 32,
            TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::Riscv64 => 64,
        }
    }

    /// Create an LLVM module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_module(&self, name: &str) -> Result<(), CompileError> {
        // Create module with the context
        let module = self.context.create_module(name);

        // Set target triple
        let triple = self.get_target_triple();
        module.set_triple(&inkwell::targets::TargetTriple::create(&triple));

        // Store module (using unsafe to extend lifetime - this is safe because
        // the module is owned by the backend and won't outlive the context)
        let module_static: Module<'static> = unsafe { std::mem::transmute(module) };
        *self.module.borrow_mut() = Some(module_static);

        // Create builder
        let builder = self.context.create_builder();
        let builder_static: Builder<'static> = unsafe { std::mem::transmute(builder) };
        *self.builder.borrow_mut() = Some(builder_static);

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_module(&self, _name: &str) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Create LLVM function signature (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_function_signature(
        &self,
        name: &str,
        param_types: &[TypeId],
        return_type: &TypeId,
    ) -> Result<FunctionValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        // Map parameter types
        let param_llvm: Result<Vec<_>, _> = param_types
            .iter()
            .map(|ty| self.llvm_type(ty).map(|t| t.into()))
            .collect();
        let param_llvm = param_llvm?;

        // Map return type
        let ret_llvm = self.llvm_type(return_type)?;

        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => t.fn_type(&param_llvm, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&param_llvm, false),
            BasicTypeEnum::PointerType(t) => t.fn_type(&param_llvm, false),
            _ => {
                return Err(CompileError::Semantic(
                    "Unsupported return type".to_string(),
                ))
            }
        };

        Ok(module.add_function(name, fn_type, None))
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_function_signature(
        &self,
        _name: &str,
        _param_types: &[TypeId],
        _return_type: &TypeId,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Get LLVM IR as string (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        Ok(module.print_to_string().to_string())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Verify the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn verify(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        module
            .verify()
            .map_err(|e| CompileError::Semantic(format!("LLVM verification failed: {}", e)))?;
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn verify(&self) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Compile a MIR function to LLVM IR (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_function(&self, func: &MirFunction) -> Result<(), CompileError> {
        use crate::mir::instructions::MirInst;
        use std::collections::HashMap;

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;

        // Map parameter types
        let param_types: Result<Vec<_>, _> = func
            .params
            .iter()
            .map(|p| self.llvm_type(&p.ty).map(|t| t.into()))
            .collect();
        let param_types = param_types?;

        // Map return type
        let ret_llvm = self.llvm_type(&func.return_type)?;

        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
            BasicTypeEnum::PointerType(t) => t.fn_type(&param_types, false),
            _ => {
                return Err(CompileError::Semantic(
                    "Unsupported return type".to_string(),
                ))
            }
        };

        // Add function to module
        let function = module.add_function(&func.name, fn_type, None);

        // Create basic blocks for each MIR block
        let mut llvm_blocks = HashMap::new();
        for block in &func.blocks {
            let bb = self
                .context
                .append_basic_block(function, &format!("bb{}", block.id.0));
            llvm_blocks.insert(block.id, bb);
        }

        // Map virtual registers to LLVM values
        let mut vreg_map: HashMap<crate::mir::instructions::VReg, inkwell::values::BasicValueEnum> =
            HashMap::new();

        // Map function parameters to virtual registers
        for (i, param) in func.params.iter().enumerate() {
            if let Some(llvm_param) = function.get_nth_param(i as u32) {
                // Params are mapped to vregs starting from VReg(0)
                vreg_map.insert(crate::mir::instructions::VReg(i as u32), llvm_param.into());
            }
        }

        // Compile each block
        for block in &func.blocks {
            let bb = llvm_blocks[&block.id];
            builder.position_at_end(bb);

            // Compile each instruction
            for inst in &block.instructions {
                match inst {
                    MirInst::ConstInt { dest, value } => {
                        let const_val = self.context.i64_type().const_int(*value as u64, true);
                        vreg_map.insert(*dest, const_val.into());
                    }
                    MirInst::ConstBool { dest, value } => {
                        let const_val = self.context.bool_type().const_int(*value as u64, false);
                        vreg_map.insert(*dest, const_val.into());
                    }
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
                        let left_val = vreg_map.get(left).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", left))
                        })?;
                        let right_val = vreg_map.get(right).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", right))
                        })?;

                        let result = self.compile_binop(*op, *left_val, *right_val, builder)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::ConstFloat { dest, value } => {
                        let const_val = self.context.f64_type().const_float(*value);
                        vreg_map.insert(*dest, const_val.into());
                    }
                    MirInst::UnaryOp { dest, op, operand } => {
                        let operand_val = vreg_map.get(operand).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", operand))
                        })?;

                        let result = self.compile_unaryop(*op, *operand_val, builder)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::Load { dest, addr, ty } => {
                        let addr_val = vreg_map.get(addr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", addr))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
                            let loaded = builder
                                .build_load(self.llvm_type(ty)?, *ptr, "load")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;
                            vreg_map.insert(*dest, loaded);
                        } else {
                            return Err(CompileError::Semantic(
                                "Load requires pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::Store { addr, value, ty: _ } => {
                        let addr_val = vreg_map.get(addr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", addr))
                        })?;
                        let value_val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
                            builder.build_store(*ptr, *value_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        } else {
                            return Err(CompileError::Semantic(
                                "Store requires pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::GcAlloc { dest, ty } => {
                        // Allocate on stack for now (proper GC integration later)
                        let llvm_ty = self.llvm_type(ty)?;
                        let alloc = builder.build_alloca(llvm_ty, "gc_alloc").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::ConstString { dest, value } => {
                        // Create global string constant
                        let str_val = self.context.const_string(value.as_bytes(), false);
                        let global = module.add_global(str_val.get_type(), None, "str");
                        global.set_initializer(&str_val);
                        global.set_constant(true);
                        vreg_map.insert(*dest, global.as_pointer_value().into());
                    }
                    _ => {
                        // Other instructions not yet implemented
                    }
                }
            }

            // Compile terminator
            if let Some(term) = &block.terminator {
                self.compile_terminator(term, &llvm_blocks, &vreg_map, builder)?;
            }
        }

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Compile a binary operation
    #[cfg(feature = "llvm")]
    fn compile_binop(
        &self,
        op: crate::mir::instructions::BinOpKind,
        left: inkwell::values::BasicValueEnum,
        right: inkwell::values::BasicValueEnum,
        builder: &Builder,
    ) -> Result<inkwell::values::BasicValueEnum, CompileError> {
        use crate::mir::instructions::BinOpKind;

        // Both operands must be the same type
        match (left, right) {
            (
                inkwell::values::BasicValueEnum::IntValue(l),
                inkwell::values::BasicValueEnum::IntValue(r),
            ) => {
                let result = match op {
                    BinOpKind::Add => builder
                        .build_int_add(l, r, "add")
                        .map_err(|e| CompileError::Semantic(format!("build_int_add: {}", e)))?,
                    BinOpKind::Sub => builder
                        .build_int_sub(l, r, "sub")
                        .map_err(|e| CompileError::Semantic(format!("build_int_sub: {}", e)))?,
                    BinOpKind::Mul => builder
                        .build_int_mul(l, r, "mul")
                        .map_err(|e| CompileError::Semantic(format!("build_int_mul: {}", e)))?,
                    BinOpKind::Div => builder
                        .build_int_signed_div(l, r, "div")
                        .map_err(|e| {
                            CompileError::Semantic(format!("build_int_signed_div: {}", e))
                        })?,
                    BinOpKind::Eq => builder
                        .build_int_compare(IntPredicate::EQ, l, r, "eq")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOpKind::Ne => builder
                        .build_int_compare(IntPredicate::NE, l, r, "ne")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOpKind::Lt => builder
                        .build_int_compare(IntPredicate::SLT, l, r, "lt")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOpKind::Le => builder
                        .build_int_compare(IntPredicate::SLE, l, r, "le")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOpKind::Gt => builder
                        .build_int_compare(IntPredicate::SGT, l, r, "gt")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOpKind::Ge => builder
                        .build_int_compare(IntPredicate::SGE, l, r, "ge")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    _ => {
                        return Err(CompileError::Semantic(format!(
                            "Unsupported integer binop: {:?}",
                            op
                        )))
                    }
                };
                Ok(result.into())
            }
            (
                inkwell::values::BasicValueEnum::FloatValue(l),
                inkwell::values::BasicValueEnum::FloatValue(r),
            ) => {
                let result = match op {
                    BinOpKind::Add => builder
                        .build_float_add(l, r, "fadd")
                        .map_err(|e| CompileError::Semantic(format!("build_float_add: {}", e)))?,
                    BinOpKind::Sub => builder
                        .build_float_sub(l, r, "fsub")
                        .map_err(|e| CompileError::Semantic(format!("build_float_sub: {}", e)))?,
                    BinOpKind::Mul => builder
                        .build_float_mul(l, r, "fmul")
                        .map_err(|e| CompileError::Semantic(format!("build_float_mul: {}", e)))?,
                    BinOpKind::Div => builder
                        .build_float_div(l, r, "fdiv")
                        .map_err(|e| CompileError::Semantic(format!("build_float_div: {}", e)))?,
                    _ => {
                        return Err(CompileError::Semantic(format!(
                            "Unsupported float binop: {:?}",
                            op
                        )))
                    }
                };
                Ok(result.into())
            }
            _ => Err(CompileError::Semantic(
                "Type mismatch in binary operation".to_string(),
            )),
        }
    }

    /// Compile a unary operation
    #[cfg(feature = "llvm")]
    fn compile_unaryop(
        &self,
        op: crate::mir::instructions::UnaryOpKind,
        operand: inkwell::values::BasicValueEnum,
        builder: &Builder,
    ) -> Result<inkwell::values::BasicValueEnum, CompileError> {
        use crate::mir::instructions::UnaryOpKind;

        match operand {
            inkwell::values::BasicValueEnum::IntValue(val) => {
                let result = match op {
                    UnaryOpKind::Neg => builder
                        .build_int_neg(val, "neg")
                        .map_err(|e| CompileError::Semantic(format!("build_int_neg: {}", e)))?,
                    UnaryOpKind::Not => builder
                        .build_not(val, "not")
                        .map_err(|e| CompileError::Semantic(format!("build_not: {}", e)))?,
                    _ => {
                        return Err(CompileError::Semantic(format!(
                            "Unsupported integer unary op: {:?}",
                            op
                        )))
                    }
                };
                Ok(result.into())
            }
            inkwell::values::BasicValueEnum::FloatValue(val) => {
                let result = match op {
                    UnaryOpKind::Neg => builder
                        .build_float_neg(val, "fneg")
                        .map_err(|e| CompileError::Semantic(format!("build_float_neg: {}", e)))?,
                    _ => {
                        return Err(CompileError::Semantic(format!(
                            "Unsupported float unary op: {:?}",
                            op
                        )))
                    }
                };
                Ok(result.into())
            }
            _ => Err(CompileError::Semantic(
                "Invalid operand type for unary operation".to_string(),
            )),
        }
    }

    /// Compile a terminator instruction
    #[cfg(feature = "llvm")]
    fn compile_terminator(
        &self,
        term: &crate::mir::instructions::Terminator,
        llvm_blocks: &std::collections::HashMap<
            crate::mir::instructions::BlockId,
            inkwell::basic_block::BasicBlock,
        >,
        vreg_map: &std::collections::HashMap<
            crate::mir::instructions::VReg,
            inkwell::values::BasicValueEnum,
        >,
        builder: &Builder,
    ) -> Result<(), CompileError> {
        use crate::mir::instructions::Terminator;

        match term {
            Terminator::Return(vreg) => {
                if let Some(val) = vreg_map.get(vreg) {
                    builder
                        .build_return(Some(val))
                        .map_err(|e| CompileError::Semantic(format!("build_return: {}", e)))?;
                } else {
                    return Err(CompileError::Semantic(format!(
                        "Undefined return value: {:?}",
                        vreg
                    )));
                }
            }
            Terminator::ReturnVoid => {
                builder
                    .build_return(None)
                    .map_err(|e| CompileError::Semantic(format!("build_return: {}", e)))?;
            }
            Terminator::Jump(block_id) => {
                let target_bb = llvm_blocks.get(block_id).ok_or_else(|| {
                    CompileError::Semantic(format!("Undefined block: {:?}", block_id))
                })?;
                builder
                    .build_unconditional_branch(*target_bb)
                    .map_err(|e| {
                        CompileError::Semantic(format!("build_unconditional_branch: {}", e))
                    })?;
            }
            Terminator::Branch {
                cond,
                then_block,
                else_block,
            } => {
                let cond_val = vreg_map.get(cond).ok_or_else(|| {
                    CompileError::Semantic(format!("Undefined condition: {:?}", cond))
                })?;

                if let inkwell::values::BasicValueEnum::IntValue(cond_int) = cond_val {
                    let then_bb = llvm_blocks.get(then_block).ok_or_else(|| {
                        CompileError::Semantic(format!("Undefined block: {:?}", then_block))
                    })?;
                    let else_bb = llvm_blocks.get(else_block).ok_or_else(|| {
                        CompileError::Semantic(format!("Undefined block: {:?}", else_block))
                    })?;

                    builder
                        .build_conditional_branch(*cond_int, *then_bb, *else_bb)
                        .map_err(|e| {
                            CompileError::Semantic(format!("build_conditional_branch: {}", e))
                        })?;
                } else {
                    return Err(CompileError::Semantic(
                        "Branch condition must be boolean".to_string(),
                    ));
                }
            }
            _ => {
                return Err(CompileError::Semantic(format!(
                    "Unsupported terminator: {:?}",
                    term
                )))
            }
        }

        Ok(())
    }

    /// Emit object code from the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // Initialize LLVM targets
        LlvmTarget::initialize_all(&InitializationConfig::default());

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        // Get target triple
        let triple = self.get_target_triple();
        let target_triple = inkwell::targets::TargetTriple::create(&triple);

        // Get target from triple
        let target = LlvmTarget::from_triple(&target_triple).map_err(|e| {
            CompileError::Semantic(format!("Failed to create target from triple: {}", e))
        })?;

        // Create target machine
        let target_machine = target
            .create_target_machine(
                &target_triple,
                "generic",
                "",
                OptimizationLevel::Default,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or_else(|| CompileError::Semantic("Failed to create target machine".to_string()))?;

        // Emit object file to memory buffer
        let buffer = target_machine
            .write_to_memory_buffer(module, FileType::Object)
            .map_err(|e| CompileError::Semantic(format!("Failed to emit object file: {}", e)))?;

        Ok(buffer.as_slice().to_vec())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Helper for creating test functions with binary operations on constants
    /// 
    /// Sets up a function with signature `i64 fn()`, creates two i64 constants,
    /// applies an operation via the provided closure, and returns the result.
    #[cfg(feature = "llvm")]
    fn setup_test_function<F>(
        &self,
        name: &str,
        a_val: i64,
        b_val: i64,
        build_op: F,
    ) -> Result<(), CompileError>
    where
        F: FnOnce(&Builder, inkwell::values::IntValue, inkwell::values::IntValue) -> Result<inkwell::values::IntValue, CompileError>,
    {
        let (module, builder) = self.get_module_and_builder()?;
        
        // Create function signature: i64 fn()
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        let function = module.add_function(name, fn_type, None);

        // Create entry block
        let entry = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry);

        // Create constants
        let a = i64_type.const_int(a_val as u64, true);
        let b = i64_type.const_int(b_val as u64, true);

        // Build operation
        let result = build_op(builder, a, b)?;

        // Return result
        builder
            .build_return(Some(&result))
            .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;

        Ok(())
    }

    /// Helper to get module and builder references for test functions
    #[cfg(feature = "llvm")]
    fn get_module_and_builder(&self) -> Result<(&Module, &Builder), CompileError> {
        self.create_module("test_module")?;

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;

        Ok((module, builder))
    }

    /// Compile a simple arithmetic function for testing
    #[cfg(feature = "llvm")]
    pub fn compile_simple_function(
        &self,
        name: &str,
        a_val: i64,
        b_val: i64,
    ) -> Result<(), CompileError> {
        self.setup_test_function(name, a_val, b_val, |builder, a, b| {
            builder
                .build_int_add(a, b, "add")
                .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e)))
        })
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_simple_function(
        &self,
        _name: &str,
        _a_val: i64,
        _b_val: i64,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Compile a function with binary operations (for testing)
    #[cfg(feature = "llvm")]
    pub fn compile_binop_function(
        &self,
        name: &str,
        op: BinOp,
        a_val: i64,
        b_val: i64,
    ) -> Result<(), CompileError> {
        self.setup_test_function(name, a_val, b_val, |builder, a, b| {
            match op {
                BinOp::Add => builder
                    .build_int_add(a, b, "add")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e))),
                BinOp::Sub => builder
                    .build_int_sub(a, b, "sub")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build sub: {}", e))),
                BinOp::Mul => builder
                    .build_int_mul(a, b, "mul")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build mul: {}", e))),
                BinOp::Div => builder
                    .build_int_signed_div(a, b, "div")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build div: {}", e))),
            }
        })
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_binop_function(
        &self,
        _name: &str,
        _op: BinOp,
        _a_val: i64,
        _b_val: i64,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Compile a function with conditional logic (for testing)
    #[cfg(feature = "llvm")]
    pub fn compile_conditional_function(
        &self,
        name: &str,
        cond_val: bool,
        then_val: i64,
        else_val: i64,
    ) -> Result<(), CompileError> {
        let (module, builder) = self.get_module_and_builder()?;

        // Create function signature: i64 fn()
        let i64_type = self.context.i64_type();
        let bool_type = self.context.bool_type();
        let fn_type = i64_type.fn_type(&[], false);
        let function = module.add_function(name, fn_type, None);

        // Create blocks
        let entry = self.context.append_basic_block(function, "entry");
        let then_bb = self.context.append_basic_block(function, "then");
        let else_bb = self.context.append_basic_block(function, "else");
        let merge_bb = self.context.append_basic_block(function, "merge");

        // Entry block
        builder.position_at_end(entry);
        let cond = bool_type.const_int(cond_val as u64, false);
        builder
            .build_conditional_branch(cond, then_bb, else_bb)
            .map_err(|e| {
                CompileError::Semantic(format!("Failed to build conditional branch: {}", e))
            })?;

        // Then block
        builder.position_at_end(then_bb);
        let then_value = i64_type.const_int(then_val as u64, true);
        builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| {
                CompileError::Semantic(format!("Failed to build unconditional branch: {}", e))
            })?;

        // Else block
        builder.position_at_end(else_bb);
        let else_value = i64_type.const_int(else_val as u64, true);
        builder
            .build_unconditional_branch(merge_bb)
            .map_err(|e| {
                CompileError::Semantic(format!("Failed to build unconditional branch: {}", e))
            })?;

        // Merge block with phi
        builder.position_at_end(merge_bb);
        let phi = builder
            .build_phi(i64_type, "result")
            .map_err(|e| CompileError::Semantic(format!("Failed to build phi: {}", e)))?;
        phi.add_incoming(&[(&then_value, then_bb), (&else_value, else_bb)]);

        let result = phi.as_basic_value();
        builder
            .build_return(Some(&result))
            .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_conditional_function(
        &self,
        _name: &str,
        _cond_val: bool,
        _then_val: i64,
        _else_val: i64,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }
}

impl NativeBackend for LlvmBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        let module_name = module.name.as_deref().unwrap_or("module");
        self.create_module(module_name)?;
        for func in &module.functions {
            self.compile_function(func)?;
        }
        self.verify()?;
        self.emit_object(module)
    }

    fn name(&self) -> &'static str {
        "llvm"
    }

    fn supports_target(target: &Target) -> bool {
        // LLVM supports all targets
        use simple_common::target::TargetArch;
        matches!(
            target.arch,
            TargetArch::X86_64
                | TargetArch::Aarch64
                | TargetArch::X86
                | TargetArch::Arm
                | TargetArch::Riscv64
                | TargetArch::Riscv32
        )
    }
}
