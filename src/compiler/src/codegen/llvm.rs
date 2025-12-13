/// LLVM backend for 32-bit and 64-bit target support
///
/// This backend complements Cranelift by providing:
/// - 32-bit architecture support (i686, armv7, riscv32)
/// - Alternative 64-bit backend option
/// - Shared MIR transforms and runtime FFI specs
///
/// Requires the `llvm` feature flag and LLVM 18 toolchain to be enabled.

use crate::codegen::backend_trait::NativeBackend;
use crate::error::CompileError;
use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};
use simple_common::target::Target;

#[cfg(feature = "llvm")]
use inkwell::context::Context;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::types::{BasicTypeEnum, IntType, FloatType};
#[cfg(feature = "llvm")]
use inkwell::values::FunctionValue;
#[cfg(feature = "llvm")]
use inkwell::IntPredicate;
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

/// Binary operation types
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl LlvmBackend {
    /// Create a new LLVM backend for the given target
    pub fn new(target: Target) -> Result<Self, CompileError> {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = target; // Suppress unused warning when feature disabled
            return Err(CompileError::Semantic(
                "LLVM backend requires 'llvm' feature flag. \
                 Build with: cargo build --features llvm".to_string()
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
            TargetOS::Windows => "pc-windows-msvc",
            TargetOS::MacOS => "apple-darwin",
            TargetOS::FreeBSD => "unknown-freebsd",
            TargetOS::None => "unknown-none-elf",
            TargetOS::Any => "unknown-unknown",
        };
        
        format!("{}-{}", arch_str, os_str)
    }

    /// Get pointer width for this target
    pub fn pointer_width(&self) -> u32 {
        match self.target.arch.pointer_size() {
            simple_common::target::PointerSize::Bits32 => 32,
            simple_common::target::PointerSize::Bits64 => 64,
        }
    }

    /// Map a Simple type to an LLVM type (returns LlvmType for non-feature builds)
    pub fn map_type(&self, ty: &TypeId) -> Result<LlvmType, CompileError> {
        use crate::hir::TypeId as T;
        match *ty {
            T::I32 => Ok(LlvmType::I32),
            T::I64 => Ok(LlvmType::I64),
            T::U32 => Ok(LlvmType::I32), // LLVM doesn't distinguish signed/unsigned at type level
            T::U64 => Ok(LlvmType::I64),
            T::F32 => Ok(LlvmType::F32),
            T::F64 => Ok(LlvmType::F64),
            T::BOOL => Ok(LlvmType::I1),
            _ => Err(CompileError::Semantic(format!("Unsupported type in LLVM backend: {:?}", ty))),
        }
    }

    /// Get actual LLVM BasicTypeEnum for a TypeId (feature-gated)
    #[cfg(feature = "llvm")]
    fn llvm_type(&self, ty: &TypeId) -> Result<BasicTypeEnum<'static>, CompileError> {
        use crate::hir::TypeId as T;
        match *ty {
            T::I32 | T::U32 => Ok(self.context.i32_type().into()),
            T::I64 | T::U64 => Ok(self.context.i64_type().into()),
            T::F32 => Ok(self.context.f32_type().into()),
            T::F64 => Ok(self.context.f64_type().into()),
            T::BOOL => Ok(self.context.bool_type().into()),
            _ => Err(CompileError::Semantic(format!("Unsupported LLVM type: {:?}", ty))),
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
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Create LLVM function signature (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_function_signature(
        &self,
        name: &str,
        params: &[TypeId],
        ret_type: &TypeId,
    ) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        // Map parameter types
        let param_types: Result<Vec<_>, _> = params.iter()
            .map(|ty| self.llvm_type(ty).map(|t| t.into()))
            .collect();
        let param_types = param_types?;
        
        // Map return type
        let ret_llvm = self.llvm_type(ret_type)?;
        
        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
            _ => return Err(CompileError::Semantic("Unsupported return type".to_string())),
        };
        
        // Add function to module
        let _function = module.add_function(name, fn_type, None);
        
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_function_signature(
        &self,
        _name: &str,
        _params: &[TypeId],
        _ret_type: &TypeId,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Get LLVM IR as string (for debugging/testing)
    #[cfg(feature = "llvm")]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        Ok(module.print_to_string().to_string())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Verify the LLVM module
    #[cfg(feature = "llvm")]
    pub fn verify(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        match module.verify() {
            Ok(_) => Ok(()),
            Err(e) => Err(CompileError::Semantic(format!("LLVM verification failed: {}", e))),
        }
    }

    #[cfg(not(feature = "llvm"))]
    pub fn verify(&self) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Compile a MIR function to LLVM IR
    pub fn compile_function(&self, _func: &MirFunction) -> Result<(), CompileError> {
        // TODO: Implement function compilation
        Ok(())
    }

    /// Emit object code for a module
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // TODO: Implement object emission
        Ok(vec![])
    }

    /// Compile a simple function with body (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_simple_function(
        &self,
        name: &str,
        params: &[TypeId],
        ret_type: &TypeId,
        constant_return: i32,
    ) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        let builder = self.builder.borrow();
        let builder = builder.as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;
        
        // Map parameter types
        let param_types: Result<Vec<_>, _> = params.iter()
            .map(|ty| self.llvm_type(ty).map(|t| t.into()))
            .collect();
        let param_types = param_types?;
        
        // Map return type
        let ret_llvm = self.llvm_type(ret_type)?;
        
        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => t.fn_type(&param_types, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&param_types, false),
            _ => return Err(CompileError::Semantic("Unsupported return type".to_string())),
        };
        
        // Add function to module
        let function = module.add_function(name, fn_type, None);
        
        // Create entry basic block
        let entry_block = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry_block);
        
        // Create constant return value
        let ret_value = match ret_llvm {
            BasicTypeEnum::IntType(t) => {
                t.const_int(constant_return as u64, false)
            },
            _ => return Err(CompileError::Semantic("Only int return for now".to_string())),
        };
        
        // Build return instruction
        builder.build_return(Some(&ret_value))
            .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;
        
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_simple_function(
        &self,
        _name: &str,
        _params: &[TypeId],
        _ret_type: &TypeId,
        _constant_return: i32,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Compile a function with binary operation (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_binop_function(
        &self,
        name: &str,
        param1_ty: &TypeId,
        param2_ty: &TypeId,
        ret_type: &TypeId,
        op: BinOp,
    ) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        let builder = self.builder.borrow();
        let builder = builder.as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;
        
        // Map parameter types
        let p1_llvm = self.llvm_type(param1_ty)?;
        let p2_llvm = self.llvm_type(param2_ty)?;
        let ret_llvm = self.llvm_type(ret_type)?;
        
        // Create function type
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => {
                t.fn_type(&[p1_llvm.into(), p2_llvm.into()], false)
            },
            BasicTypeEnum::FloatType(t) => {
                t.fn_type(&[p1_llvm.into(), p2_llvm.into()], false)
            },
            _ => return Err(CompileError::Semantic("Unsupported return type".to_string())),
        };
        
        // Add function to module
        let function = module.add_function(name, fn_type, None);
        
        // Create entry basic block
        let entry_block = self.context.append_basic_block(function, "entry");
        builder.position_at_end(entry_block);
        
        // Get function parameters
        let param1 = function.get_nth_param(0)
            .ok_or_else(|| CompileError::Semantic("Missing param 0".to_string()))?;
        let param2 = function.get_nth_param(1)
            .ok_or_else(|| CompileError::Semantic("Missing param 1".to_string()))?;
        
        // Build binary operation
        let result = match (&ret_llvm, op) {
            (BasicTypeEnum::IntType(_), BinOp::Add) => {
                builder.build_int_add(param1.into_int_value(), param2.into_int_value(), "add")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::IntType(_), BinOp::Sub) => {
                builder.build_int_sub(param1.into_int_value(), param2.into_int_value(), "sub")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build sub: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::IntType(_), BinOp::Mul) => {
                builder.build_int_mul(param1.into_int_value(), param2.into_int_value(), "mul")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build mul: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::IntType(_), BinOp::Div) => {
                builder.build_int_signed_div(param1.into_int_value(), param2.into_int_value(), "div")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build div: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::FloatType(_), BinOp::Add) => {
                builder.build_float_add(param1.into_float_value(), param2.into_float_value(), "fadd")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build fadd: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::FloatType(_), BinOp::Sub) => {
                builder.build_float_sub(param1.into_float_value(), param2.into_float_value(), "fsub")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build fsub: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::FloatType(_), BinOp::Mul) => {
                builder.build_float_mul(param1.into_float_value(), param2.into_float_value(), "fmul")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build fmul: {}", e)))?
                    .into()
            },
            (BasicTypeEnum::FloatType(_), BinOp::Div) => {
                builder.build_float_div(param1.into_float_value(), param2.into_float_value(), "fdiv")
                    .map_err(|e| CompileError::Semantic(format!("Failed to build fdiv: {}", e)))?
                    .into()
            },
            _ => return Err(CompileError::Semantic(format!("Unsupported binop: {:?}", op))),
        };
        
        // Build return instruction
        builder.build_return(Some(&result))
            .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;
        
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_binop_function(
        &self,
        _name: &str,
        _param1_ty: &TypeId,
        _param2_ty: &TypeId,
        _ret_type: &TypeId,
        _op: BinOp,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }

    /// Compile a function with conditional (if-else) (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn compile_conditional_function(
        &self,
        name: &str,
        param_ty: &TypeId,
        ret_type: &TypeId,
        true_value: i32,
        false_value: i32,
    ) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module.as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        
        let builder = self.builder.borrow();
        let builder = builder.as_ref()
            .ok_or_else(|| CompileError::Semantic("Builder not created".to_string()))?;
        
        // Map types
        let param_llvm = self.llvm_type(param_ty)?;
        let ret_llvm = self.llvm_type(ret_type)?;
        
        // Create function type: fn(i32) -> i32
        let fn_type = match ret_llvm {
            BasicTypeEnum::IntType(t) => {
                t.fn_type(&[param_llvm.into()], false)
            },
            _ => return Err(CompileError::Semantic("Unsupported return type".to_string())),
        };
        
        // Add function to module
        let function = module.add_function(name, fn_type, None);
        
        // Create basic blocks
        let entry_block = self.context.append_basic_block(function, "entry");
        let then_block = self.context.append_basic_block(function, "then");
        let else_block = self.context.append_basic_block(function, "else");
        let merge_block = self.context.append_basic_block(function, "merge");
        
        // Build entry block: if (param > 0)
        builder.position_at_end(entry_block);
        let param = function.get_nth_param(0)
            .ok_or_else(|| CompileError::Semantic("Missing param".to_string()))?;
        
        let zero = self.context.i32_type().const_int(0, false);
        let cond = builder.build_int_compare(
            inkwell::IntPredicate::SGT,
            param.into_int_value(),
            zero,
            "cmp"
        ).map_err(|e| CompileError::Semantic(format!("Failed to build cmp: {}", e)))?;
        
        builder.build_conditional_branch(cond, then_block, else_block)
            .map_err(|e| CompileError::Semantic(format!("Failed to build branch: {}", e)))?;
        
        // Build then block
        builder.position_at_end(then_block);
        let then_val = self.context.i32_type().const_int(true_value as u64, false);
        builder.build_unconditional_branch(merge_block)
            .map_err(|e| CompileError::Semantic(format!("Failed to build branch: {}", e)))?;
        
        // Build else block
        builder.position_at_end(else_block);
        let else_val = self.context.i32_type().const_int(false_value as u64, false);
        builder.build_unconditional_branch(merge_block)
            .map_err(|e| CompileError::Semantic(format!("Failed to build branch: {}", e)))?;
        
        // Build merge block with phi
        builder.position_at_end(merge_block);
        let phi = builder.build_phi(self.context.i32_type(), "result")
            .map_err(|e| CompileError::Semantic(format!("Failed to build phi: {}", e)))?;
        phi.add_incoming(&[(&then_val, then_block), (&else_val, else_block)]);
        
        let phi_val = phi.as_basic_value();
        builder.build_return(Some(&phi_val))
            .map_err(|e| CompileError::Semantic(format!("Failed to build return: {}", e)))?;
        
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn compile_conditional_function(
        &self,
        _name: &str,
        _param_ty: &TypeId,
        _ret_type: &TypeId,
        _true_value: i32,
        _false_value: i32,
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }
}

/// Implement the NativeBackend trait for LLVM
impl NativeBackend for LlvmBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // Compile each function
        for func in &module.functions {
            self.compile_function(func)?;
        }
        
        // Emit object code
        self.emit_object(module)
    }

    fn name(&self) -> &'static str {
        "llvm"
    }

    fn supports_target(target: &Target) -> bool {
        // LLVM supports all architectures we care about
        // In the future, we might check for LLVM toolchain availability here
        match target.arch {
            simple_common::target::TargetArch::X86_64
            | simple_common::target::TargetArch::Aarch64
            | simple_common::target::TargetArch::X86
            | simple_common::target::TargetArch::Arm
            | simple_common::target::TargetArch::Riscv64
            | simple_common::target::TargetArch::Riscv32 => true,
        }
    }
}

/// LLVM type representation
#[derive(Debug, Clone, PartialEq)]
pub enum LlvmType {
    Void,
    I1,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Pointer(Box<LlvmType>),
    Struct(Vec<LlvmType>),
    Array(Box<LlvmType>, usize),
}
