/// LLVM backend for 32-bit and 64-bit target support
///
/// This backend complements Cranelift by providing:
/// - 32-bit architecture support (i686, armv7, riscv32)
/// - Alternative 64-bit backend option
/// - Shared MIR transforms and runtime FFI specs
///
/// Requires the `llvm` feature flag and LLVM 18 toolchain to be enabled.

mod types;
#[cfg(feature = "llvm-gpu")]
pub mod gpu;

#[cfg(feature = "llvm-gpu")]
pub use gpu::{GpuComputeCapability, LlvmGpuBackend};
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
use inkwell::types::{BasicType, BasicTypeEnum, FloatType, IntType};
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
    /// Enable coverage instrumentation
    coverage_enabled: bool,
    #[cfg(feature = "llvm")]
    context: &'static Context,
    #[cfg(feature = "llvm")]
    module: RefCell<Option<Module<'static>>>,
    #[cfg(feature = "llvm")]
    builder: RefCell<Option<Builder<'static>>>,
    /// Counter for coverage basic blocks
    #[cfg(feature = "llvm")]
    coverage_counter: RefCell<u32>,
}

// Manual Debug implementation since Context/Module/Builder don't implement Debug
impl std::fmt::Debug for LlvmBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LlvmBackend")
            .field("target", &self.target)
            .field("coverage_enabled", &self.coverage_enabled)
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
            Err(CompileError::Semantic(
                "LLVM backend requires 'llvm' feature flag. \
                 Build with: cargo build --features llvm"
                    .to_string(),
            ))
        }

        #[cfg(feature = "llvm")]
        {
            let context = Box::leak(Box::new(Context::create()));
            Ok(Self {
                target,
                coverage_enabled: false,
                context,
                module: RefCell::new(None),
                builder: RefCell::new(None),
                coverage_counter: RefCell::new(0),
            })
        }
    }

    /// Enable coverage instrumentation
    pub fn with_coverage(mut self, enabled: bool) -> Self {
        self.coverage_enabled = enabled;
        self
    }

    /// Check if coverage is enabled
    pub fn coverage_enabled(&self) -> bool {
        self.coverage_enabled
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

        *self.module.borrow_mut() = Some(module);

        // Create builder
        let builder = self.context.create_builder();
        *self.builder.borrow_mut() = Some(builder);

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
        use crate::mir::MirInst;
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

        // Create function type
        let fn_type = if func.return_type == TypeId::VOID {
            self.context.void_type().fn_type(&param_types, false)
        } else {
            let ret_llvm = self.llvm_type(&func.return_type)?;
            match ret_llvm {
                BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
                BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
                BasicTypeEnum::PointerType(t) => t.fn_type(&param_types, false),
                _ => {
                    return Err(CompileError::Semantic(
                        "Unsupported return type".to_string(),
                    ))
                }
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
        let mut vreg_map: HashMap<crate::mir::VReg, inkwell::values::BasicValueEnum<'static>> =
            HashMap::new();

        // Map function parameters to virtual registers
        for (i, param) in func.params.iter().enumerate() {
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
                    MirInst::Call { dest, target, args } => {
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
                            let val = vreg_map.get(arg).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", arg))
                            })?;
                            arg_vals.push((*val).into());
                        }

                        // Build the call
                        let call_site = builder
                            .build_call(called_func, &arg_vals, "call")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        // Store result if there's a destination
                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                    }
                    MirInst::ArrayLit { dest, elements } => {
                        // Create array on stack and initialize elements
                        let i64_type = self.context.i64_type();
                        let array_type = i64_type.array_type(elements.len() as u32);
                        let alloc = builder.build_alloca(array_type, "array").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;

                        // Store each element
                        for (i, elem) in elements.iter().enumerate() {
                            let elem_val = vreg_map.get(elem).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", elem))
                            })?;

                            let indices = [
                                self.context.i32_type().const_int(0, false),
                                self.context.i32_type().const_int(i as u64, false),
                            ];
                            let gep = unsafe {
                                builder.build_gep(array_type, alloc, &indices, "elem_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;

                            builder.build_store(gep, *elem_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::TupleLit { dest, elements } => {
                        // Tuples are similar to arrays - create struct on stack
                        let i64_type = self.context.i64_type();
                        let field_types: Vec<BasicTypeEnum> =
                            elements.iter().map(|_| i64_type.into()).collect();
                        let struct_type = self.context.struct_type(&field_types, false);
                        let alloc = builder.build_alloca(struct_type, "tuple").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;

                        // Store each element
                        for (i, elem) in elements.iter().enumerate() {
                            let elem_val = vreg_map.get(elem).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", elem))
                            })?;

                            let gep = builder
                                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to build struct gep: {}",
                                        e
                                    ))
                                })?;

                            builder.build_store(gep, *elem_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, alloc.into());
                    }
                    MirInst::IndexGet {
                        dest,
                        collection,
                        index,
                    } => {
                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;
                        let idx_val = vreg_map.get(index).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", index))
                        })?;

                        // Collection should be a pointer to array
                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
                            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                                let i64_type = self.context.i64_type();
                                let arr_type = i64_type.array_type(0); // Dynamic size

                                let indices = [
                                    self.context.i32_type().const_int(0, false),
                                    *idx,
                                ];
                                let gep = unsafe {
                                    builder.build_gep(arr_type, *ptr, &indices, "elem_ptr")
                                }
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build gep: {}", e))
                                })?;

                                let loaded = builder
                                    .build_load(i64_type, gep, "elem")
                                    .map_err(|e| {
                                        CompileError::Semantic(format!(
                                            "Failed to build load: {}",
                                            e
                                        ))
                                    })?;

                                vreg_map.insert(*dest, loaded);
                            }
                        }
                    }
                    MirInst::IndexSet {
                        collection,
                        index,
                        value,
                    } => {
                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;
                        let idx_val = vreg_map.get(index).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", index))
                        })?;
                        let val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        // Collection should be a pointer to array
                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
                            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                                let i64_type = self.context.i64_type();
                                let arr_type = i64_type.array_type(0);

                                let indices = [
                                    self.context.i32_type().const_int(0, false),
                                    *idx,
                                ];
                                let gep = unsafe {
                                    builder.build_gep(arr_type, *ptr, &indices, "elem_ptr")
                                }
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build gep: {}", e))
                                })?;

                                builder.build_store(gep, *val).map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build store: {}", e))
                                })?;
                            }
                        }
                    }
                    MirInst::InterpCall {
                        dest,
                        func_name,
                        args,
                    } => {
                        // Call interpreter bridge function rt_interp_call
                        let i64_type = self.context.i64_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        // Declare rt_interp_call if not exists
                        let interp_call = module.get_function("rt_interp_call").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(
                                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i8_ptr_type.into()],
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
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        if let Some(d) = dest {
                            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                vreg_map.insert(*d, ret_val);
                            }
                        }
                    }
                    MirInst::DictLit { dest, keys, values } => {
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
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build dict_new call: {}", e))
                            })?
                            .try_as_basic_value()
                            .left()
                            .ok_or_else(|| {
                                CompileError::Semantic("dict_new returned void".to_string())
                            })?;

                        // Insert each key-value pair
                        for (key, value) in keys.iter().zip(values.iter()) {
                            let key_val = vreg_map.get(key).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", key))
                            })?;
                            let value_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;

                            builder
                                .build_call(
                                    dict_insert,
                                    &[dict_ptr.into(), (*key_val).into(), (*value_val).into()],
                                    "",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to build dict_insert call: {}",
                                        e
                                    ))
                                })?;
                        }

                        vreg_map.insert(*dest, dict_ptr);
                    }
                    MirInst::StructInit {
                        dest,
                        struct_size,
                        field_offsets,
                        field_types,
                        field_values,
                        ..
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                        let array_type = i8_type.array_type(*struct_size);
                        let alloc = builder.build_alloca(array_type, "struct").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        let struct_ptr = builder
                            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                            })?;

                        for ((offset, field_type), value) in field_offsets
                            .iter()
                            .zip(field_types.iter())
                            .zip(field_values.iter())
                        {
                            let field_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;
                            let offset_val =
                                self.context.i32_type().const_int(*offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *field_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, struct_ptr.into());
                    }
                    MirInst::FieldGet {
                        dest,
                        object,
                        byte_offset,
                        field_type,
                    } => {
                        let obj_val = vreg_map.get(object).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", object))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
                            let i8_type = self.context.i8_type();
                            let i8_ptr_type =
                                self.context.ptr_type(inkwell::AddressSpace::default());
                            let base_ptr = builder
                                .build_pointer_cast(*ptr, i8_ptr_type, "struct_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                                })?;
                            let offset_val =
                                self.context.i32_type().const_int(*byte_offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            let loaded = builder
                                .build_load(llvm_field_ty, typed_ptr, "field")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;

                            vreg_map.insert(*dest, loaded);
                        } else {
                            return Err(CompileError::Semantic(
                                "FieldGet requires pointer to struct".to_string(),
                            ));
                        }
                    }
                    MirInst::FieldSet {
                        object,
                        byte_offset,
                        field_type,
                        value,
                    } => {
                        let obj_val = vreg_map.get(object).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", object))
                        })?;
                        let val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
                            let i8_type = self.context.i8_type();
                            let i8_ptr_type =
                                self.context.ptr_type(inkwell::AddressSpace::default());
                            let base_ptr = builder
                                .build_pointer_cast(*ptr, i8_ptr_type, "struct_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast struct ptr: {}", e))
                                })?;
                            let offset_val =
                                self.context.i32_type().const_int(*byte_offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "field_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast field ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        } else {
                            return Err(CompileError::Semantic(
                                "FieldSet requires pointer to struct".to_string(),
                            ));
                        }
                    }
                    MirInst::ClosureCreate {
                        dest,
                        func_name,
                        closure_size,
                        capture_offsets,
                        capture_types,
                        captures,
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                        let array_type = i8_type.array_type(*closure_size);
                        let alloc = builder.build_alloca(array_type, "closure").map_err(|e| {
                            CompileError::Semantic(format!("Failed to build alloca: {}", e))
                        })?;
                        let closure_ptr = builder
                            .build_pointer_cast(alloc, i8_ptr_type, "closure_ptr")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast closure ptr: {}", e))
                            })?;

                        let func_ptr = module
                            .get_function(func_name)
                            .map(|f| f.as_global_value().as_pointer_value())
                            .unwrap_or_else(|| i8_ptr_type.const_null());
                        let func_ptr_cast = builder
                            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast fn ptr: {}", e))
                            })?;
                        let fn_slot = builder
                            .build_pointer_cast(
                                closure_ptr,
                                i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                                "fn_slot",
                            )
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to cast fn slot: {}", e))
                            })?;
                        builder.build_store(fn_slot, func_ptr_cast).map_err(|e| {
                            CompileError::Semantic(format!("Failed to build store: {}", e))
                        })?;

                        for ((offset, field_type), value) in capture_offsets
                            .iter()
                            .zip(capture_types.iter())
                            .zip(captures.iter())
                        {
                            let capture_val = vreg_map.get(value).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                            })?;
                            let offset_val =
                                self.context.i32_type().const_int(*offset as u64, false);
                            let field_ptr = unsafe {
                                builder.build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let llvm_field_ty = self.llvm_type(field_type)?;
                            let typed_ptr = builder
                                .build_pointer_cast(
                                    field_ptr,
                                    llvm_field_ty.ptr_type(inkwell::AddressSpace::default()),
                                    "cap_typed_ptr",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast cap ptr: {}", e))
                                })?;
                            builder.build_store(typed_ptr, *capture_val).map_err(|e| {
                                CompileError::Semantic(format!("Failed to build store: {}", e))
                            })?;
                        }

                        vreg_map.insert(*dest, closure_ptr.into());
                    }
                    MirInst::IndirectCall {
                        dest,
                        callee,
                        param_types,
                        return_type,
                        args,
                        ..
                    } => {
                        let i8_type = self.context.i8_type();
                        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

                        let callee_val = vreg_map.get(callee).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", callee))
                        })?;

                        if let inkwell::values::BasicValueEnum::PointerValue(closure_ptr) =
                            callee_val
                        {
                            let base_ptr = builder
                                .build_pointer_cast(*closure_ptr, i8_ptr_type, "closure_ptr")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to cast closure ptr: {}", e))
                                })?;
                            let offset_val = self.context.i32_type().const_int(0, false);
                            let fn_ptr_slot = unsafe {
                                builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot")
                            }
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build gep: {}", e))
                            })?;
                            let fn_ptr_slot = builder
                                .build_pointer_cast(
                                    fn_ptr_slot,
                                    i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                                    "fn_ptr_slot_cast",
                                )
                                .map_err(|e| {
                                    CompileError::Semantic(format!(
                                        "Failed to cast fn slot ptr: {}",
                                        e
                                    ))
                                })?;
                            let func_ptr = builder
                                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                                .map_err(|e| {
                                    CompileError::Semantic(format!("Failed to build load: {}", e))
                                })?;

                            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> =
                                    Vec::new();
                                for arg in args {
                                    let val = vreg_map.get(arg).ok_or_else(|| {
                                        CompileError::Semantic(format!("Undefined vreg: {:?}", arg))
                                    })?;
                                    arg_vals.push((*val).into());
                                }

                                let llvm_param_types: Result<
                                    Vec<inkwell::types::BasicMetadataTypeEnum>,
                                    CompileError,
                                > = param_types
                                    .iter()
                                    .map(|ty| self.llvm_type(ty).map(|t| t.into()))
                                    .collect();
                                let llvm_param_types = llvm_param_types?;

                                let fn_type = if *return_type == TypeId::VOID {
                                    self.context
                                        .void_type()
                                        .fn_type(&llvm_param_types, false)
                                } else {
                                    let ret_llvm = self.llvm_type(return_type)?;
                                    match ret_llvm {
                                        BasicTypeEnum::IntType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
                                        BasicTypeEnum::FloatType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
                                        BasicTypeEnum::PointerType(t) => {
                                            t.fn_type(&llvm_param_types, false)
                                        }
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
                                        CompileError::Semantic(format!(
                                            "Failed to build indirect call: {}",
                                            e
                                        ))
                                    })?;

                                if let Some(d) = dest {
                                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                                        vreg_map.insert(*d, ret_val);
                                    }
                                }
                            }
                        } else {
                            return Err(CompileError::Semantic(
                                "IndirectCall requires closure pointer".to_string(),
                            ));
                        }
                    }
                    MirInst::ConstSymbol { dest, value } => {
                        // Symbols are represented as interned string pointers
                        let str_val = self.context.const_string(value.as_bytes(), false);
                        let global =
                            module.add_global(str_val.get_type(), None, &format!("sym_{}", value));
                        global.set_initializer(&str_val);
                        global.set_constant(true);
                        vreg_map.insert(*dest, global.as_pointer_value().into());
                    }
                    MirInst::SliceOp {
                        dest,
                        collection,
                        start,
                        end,
                        step,
                    } => {
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

                        let coll_val = vreg_map.get(collection).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", collection))
                        })?;

                        // Get start index (default to 0 if None)
                        let start_val = if let Some(s) = start {
                            vreg_map.get(s).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", s))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(0, false),
                            )
                        };

                        // Get end index (default to -1 meaning end of collection)
                        let end_val = if let Some(e) = end {
                            vreg_map.get(e).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", e))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(i64::MAX as u64, false),
                            )
                        };

                        // Get step (default to 1)
                        let step_val = if let Some(s) = step {
                            vreg_map.get(s).ok_or_else(|| {
                                CompileError::Semantic(format!("Undefined vreg: {:?}", s))
                            })?
                        } else {
                            &inkwell::values::BasicValueEnum::IntValue(
                                i64_type.const_int(1, false),
                            )
                        };

                        let call_site = builder
                            .build_call(
                                slice_fn,
                                &[
                                    (*coll_val).into(),
                                    (*start_val).into(),
                                    (*end_val).into(),
                                    (*step_val).into(),
                                ],
                                "slice",
                            )
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build slice call: {}", e))
                            })?;

                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*dest, ret_val);
                        }
                    }
                    MirInst::InterpEval { dest, expr_index } => {
                        // Call interpreter to evaluate expression by index
                        let i64_type = self.context.i64_type();

                        // Declare rt_interp_eval if not exists
                        let interp_eval = module.get_function("rt_interp_eval").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_interp_eval", fn_type, None)
                        });

                        let expr_index_val =
                            i64_type.const_int(*expr_index as u64, true);
                        let call_site = builder
                            .build_call(interp_eval, &[expr_index_val.into()], "eval")
                            .map_err(|e| {
                                CompileError::Semantic(format!("Failed to build call: {}", e))
                            })?;

                        if let Some(ret_val) = call_site.try_as_basic_value().left() {
                            vreg_map.insert(*dest, ret_val);
                        }
                    }
                    // GPU instructions - call runtime FFI functions
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
                        let ptr_val = vreg_map.get(ptr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", ptr))
                        })?;
                        let value_val = vreg_map.get(value).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", value))
                        })?;
                        let result = self.compile_gpu_atomic(*op, *ptr_val, *value_val, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuAtomicCmpXchg { dest, ptr, expected, desired } => {
                        let ptr_val = vreg_map.get(ptr).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", ptr))
                        })?;
                        let expected_val = vreg_map.get(expected).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", expected))
                        })?;
                        let desired_val = vreg_map.get(desired).ok_or_else(|| {
                            CompileError::Semantic(format!("Undefined vreg: {:?}", desired))
                        })?;
                        let result = self.compile_gpu_atomic_cmpxchg(*ptr_val, *expected_val, *desired_val, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    MirInst::GpuSharedAlloc { dest, element_type: _, size } => {
                        let result = self.compile_gpu_shared_alloc(*size, builder, module)?;
                        vreg_map.insert(*dest, result);
                    }
                    _ => {
                        // Other instructions not yet implemented
                    }
                }
            }

            // Compile terminator
            self.compile_terminator(&block.terminator, &llvm_blocks, &vreg_map, builder)?;
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
        op: crate::hir::BinOp,
        left: inkwell::values::BasicValueEnum<'static>,
        right: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::BinOp;

        // Both operands must be the same type
        match (left, right) {
            (
                inkwell::values::BasicValueEnum::IntValue(l),
                inkwell::values::BasicValueEnum::IntValue(r),
            ) => {
                let result = match op {
                    BinOp::Add => builder
                        .build_int_add(l, r, "add")
                        .map_err(|e| CompileError::Semantic(format!("build_int_add: {}", e)))?,
                    BinOp::Sub => builder
                        .build_int_sub(l, r, "sub")
                        .map_err(|e| CompileError::Semantic(format!("build_int_sub: {}", e)))?,
                    BinOp::Mul => builder
                        .build_int_mul(l, r, "mul")
                        .map_err(|e| CompileError::Semantic(format!("build_int_mul: {}", e)))?,
                    BinOp::Div => builder
                        .build_int_signed_div(l, r, "div")
                        .map_err(|e| {
                            CompileError::Semantic(format!("build_int_signed_div: {}", e))
                        })?,
                    BinOp::Eq => builder
                        .build_int_compare(IntPredicate::EQ, l, r, "eq")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOp::NotEq => builder
                        .build_int_compare(IntPredicate::NE, l, r, "ne")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOp::Lt => builder
                        .build_int_compare(IntPredicate::SLT, l, r, "lt")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOp::LtEq => builder
                        .build_int_compare(IntPredicate::SLE, l, r, "le")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOp::Gt => builder
                        .build_int_compare(IntPredicate::SGT, l, r, "gt")
                        .map_err(|e| CompileError::Semantic(format!("build_int_compare: {}", e)))?,
                    BinOp::GtEq => builder
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
                    BinOp::Add => builder
                        .build_float_add(l, r, "fadd")
                        .map_err(|e| CompileError::Semantic(format!("build_float_add: {}", e)))?,
                    BinOp::Sub => builder
                        .build_float_sub(l, r, "fsub")
                        .map_err(|e| CompileError::Semantic(format!("build_float_sub: {}", e)))?,
                    BinOp::Mul => builder
                        .build_float_mul(l, r, "fmul")
                        .map_err(|e| CompileError::Semantic(format!("build_float_mul: {}", e)))?,
                    BinOp::Div => builder
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
        op: crate::hir::UnaryOp,
        operand: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::UnaryOp;

        match operand {
            inkwell::values::BasicValueEnum::IntValue(val) => {
                let result = match op {
                    UnaryOp::Neg => builder
                        .build_int_neg(val, "neg")
                        .map_err(|e| CompileError::Semantic(format!("build_int_neg: {}", e)))?,
                    UnaryOp::Not => builder
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
                    UnaryOp::Neg => builder
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
        term: &crate::mir::Terminator,
        llvm_blocks: &std::collections::HashMap<
            crate::mir::BlockId,
            inkwell::basic_block::BasicBlock,
        >,
        vreg_map: &std::collections::HashMap<
            crate::mir::VReg,
            inkwell::values::BasicValueEnum<'static>,
        >,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        use crate::mir::Terminator;

        match term {
            Terminator::Return(Some(vreg)) => {
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
            Terminator::Return(None) => {
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
            Terminator::Unreachable => {
                builder
                    .build_unreachable()
                    .map_err(|e| CompileError::Semantic(format!("build_unreachable: {}", e)))?;
            }
        }

        Ok(())
    }

    /// Emit a coverage counter increment for a basic block
    #[cfg(feature = "llvm")]
    fn emit_coverage_counter(
        &self,
        module: &Module,
        builder: &Builder,
        func_name: &str,
        block_id: u32,
    ) -> Result<(), CompileError> {
        // Get next counter id
        let counter_id = {
            let mut counter = self.coverage_counter.borrow_mut();
            let id = *counter;
            *counter += 1;
            id
        };

        // Create global counter variable name
        let counter_name = format!("__simple_cov_{}_{}", func_name, block_id);

        // Check if counter already exists, if not create it
        let counter_global = if let Some(global) = module.get_global(&counter_name) {
            global
        } else {
            let i64_type = self.context.i64_type();
            let global = module.add_global(i64_type, None, &counter_name);
            global.set_initializer(&i64_type.const_zero());
            global.set_linkage(inkwell::module::Linkage::Internal);
            global
        };

        // Load current value
        let i64_type = self.context.i64_type();
        let current = builder
            .build_load(i64_type, counter_global.as_pointer_value(), "cov_load")
            .map_err(|e| CompileError::Semantic(format!("Failed to load coverage counter: {}", e)))?;

        // Increment
        if let inkwell::values::BasicValueEnum::IntValue(current_int) = current {
            let one = i64_type.const_int(1, false);
            let incremented = builder
                .build_int_add(current_int, one, "cov_inc")
                .map_err(|e| {
                    CompileError::Semantic(format!("Failed to increment coverage counter: {}", e))
                })?;

            // Store back
            builder
                .build_store(counter_global.as_pointer_value(), incremented)
                .map_err(|e| {
                    CompileError::Semantic(format!("Failed to store coverage counter: {}", e))
                })?;
        }

        // Track counter for later retrieval
        let _ = counter_id; // Will be used in coverage mapping later

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

    // ========================
    // GPU instruction helpers
    // ========================

    /// Compile GPU global_id intrinsic - returns global work item ID for dimension
    #[cfg(feature = "llvm")]
    fn compile_gpu_global_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        // Declare rt_gpu_global_id if not exists
        let gpu_global_id = module.get_function("rt_gpu_global_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_global_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_global_id, &[dim_val.into()], "global_id")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_global_id returned void".to_string()))
    }

    /// Compile GPU local_id intrinsic - returns local work item ID within workgroup
    #[cfg(feature = "llvm")]
    fn compile_gpu_local_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_local_id = module.get_function("rt_gpu_local_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_local_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_local_id, &[dim_val.into()], "local_id")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_local_id returned void".to_string()))
    }

    /// Compile GPU group_id intrinsic - returns workgroup ID
    #[cfg(feature = "llvm")]
    fn compile_gpu_group_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_group_id = module.get_function("rt_gpu_group_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_group_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_group_id, &[dim_val.into()], "group_id")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_group_id returned void".to_string()))
    }

    /// Compile GPU global_size intrinsic - returns total number of work items
    #[cfg(feature = "llvm")]
    fn compile_gpu_global_size(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_global_size = module.get_function("rt_gpu_global_size").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_global_size", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_global_size, &[dim_val.into()], "global_size")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_global_size returned void".to_string()))
    }

    /// Compile GPU local_size intrinsic - returns workgroup size
    #[cfg(feature = "llvm")]
    fn compile_gpu_local_size(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_local_size = module.get_function("rt_gpu_local_size").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_local_size", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_local_size, &[dim_val.into()], "local_size")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_local_size returned void".to_string()))
    }

    /// Compile GPU num_groups intrinsic - returns number of workgroups
    #[cfg(feature = "llvm")]
    fn compile_gpu_num_groups(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_num_groups = module.get_function("rt_gpu_num_groups").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_num_groups", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_num_groups, &[dim_val.into()], "num_groups")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_num_groups returned void".to_string()))
    }

    /// Compile GPU barrier intrinsic - synchronize all threads in workgroup
    #[cfg(feature = "llvm")]
    fn compile_gpu_barrier(
        &self,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let void_type = self.context.void_type();

        let gpu_barrier = module.get_function("rt_gpu_barrier").unwrap_or_else(|| {
            let fn_type = void_type.fn_type(&[], false);
            module.add_function("rt_gpu_barrier", fn_type, None)
        });

        builder
            .build_call(gpu_barrier, &[], "barrier")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        Ok(())
    }

    /// Compile GPU mem_fence intrinsic - memory fence with given scope
    #[cfg(feature = "llvm")]
    fn compile_gpu_mem_fence(
        &self,
        scope: crate::mir::GpuMemoryScope,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use crate::mir::GpuMemoryScope;

        let void_type = self.context.void_type();
        let i32_type = self.context.i32_type();

        let gpu_mem_fence = module.get_function("rt_gpu_mem_fence").unwrap_or_else(|| {
            let fn_type = void_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_mem_fence", fn_type, None)
        });

        let scope_val = match scope {
            GpuMemoryScope::WorkGroup => i32_type.const_int(0, false),
            GpuMemoryScope::Device => i32_type.const_int(1, false),
            GpuMemoryScope::All => i32_type.const_int(2, false),
        };

        builder
            .build_call(gpu_mem_fence, &[scope_val.into()], "mem_fence")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        Ok(())
    }

    /// Compile GPU atomic operation
    #[cfg(feature = "llvm")]
    fn compile_gpu_atomic(
        &self,
        op: crate::mir::GpuAtomicOp,
        ptr: inkwell::values::BasicValueEnum<'static>,
        value: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::mir::GpuAtomicOp;

        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Select the appropriate atomic function based on operation
        let func_name = match op {
            GpuAtomicOp::Add => "rt_gpu_atomic_add_i64",
            GpuAtomicOp::Sub => "rt_gpu_atomic_sub_i64",
            GpuAtomicOp::Xchg => "rt_gpu_atomic_xchg_i64",
            GpuAtomicOp::Min => "rt_gpu_atomic_min_i64",
            GpuAtomicOp::Max => "rt_gpu_atomic_max_i64",
            GpuAtomicOp::And => "rt_gpu_atomic_and_i64",
            GpuAtomicOp::Or => "rt_gpu_atomic_or_i64",
            GpuAtomicOp::Xor => "rt_gpu_atomic_xor_i64",
        };

        // All atomics take 2 arguments: ptr, value
        let atomic_fn = module.get_function(func_name).unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i8_ptr_type.into(), i64_type.into()], false);
            module.add_function(func_name, fn_type, None)
        });

        let call_site = builder
            .build_call(atomic_fn, &[ptr.into(), value.into()], "atomic")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("Atomic operation returned void".to_string()))
    }

    /// Compile GPU atomic compare-exchange operation
    #[cfg(feature = "llvm")]
    fn compile_gpu_atomic_cmpxchg(
        &self,
        ptr: inkwell::values::BasicValueEnum<'static>,
        expected: inkwell::values::BasicValueEnum<'static>,
        desired: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // CmpXchg takes 3 arguments: ptr, expected, desired
        let cmpxchg_fn = module.get_function("rt_gpu_atomic_cmpxchg_i64").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            module.add_function("rt_gpu_atomic_cmpxchg_i64", fn_type, None)
        });

        let call_site = builder
            .build_call(cmpxchg_fn, &[ptr.into(), expected.into(), desired.into()], "cmpxchg")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("CmpXchg operation returned void".to_string()))
    }

    /// Compile GPU shared memory allocation
    #[cfg(feature = "llvm")]
    fn compile_gpu_shared_alloc(
        &self,
        size: u32,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        let gpu_shared_alloc = module.get_function("rt_gpu_shared_alloc").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_gpu_shared_alloc", fn_type, None)
        });

        let size_val = i64_type.const_int(size as u64, false);
        let call_site = builder
            .build_call(gpu_shared_alloc, &[size_val.into()], "shared_alloc")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_shared_alloc returned void".to_string()))
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

// Test helper methods for LLVM backend.
#[cfg(feature = "llvm-tests")]
include!("../llvm_test_utils.rs");
