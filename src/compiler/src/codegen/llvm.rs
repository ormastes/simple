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

/// LLVM-based code generator
#[derive(Debug)]
pub struct LlvmBackend {
    target: Target,
    #[cfg(feature = "llvm")]
    context: Context,
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
            // TODO: Validate target triple support
            Ok(Self {
                target,
                context: Context::create(),
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

    /// Map a Simple type to an LLVM type
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

    /// Create an LLVM module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_module(&self, name: &str) -> Result<(), CompileError> {
        // Create module with the context
        let _module = self.context.create_module(name);
        // TODO: Store module for later use
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
        _name: &str,
        params: &[TypeId],
        ret_type: &TypeId,
    ) -> Result<(), CompileError> {
        // Map parameter types
        let _param_types: Result<Vec<_>, _> = params.iter()
            .map(|ty| self.map_type(ty))
            .collect();
        
        // Map return type
        let _ret = self.map_type(ret_type)?;
        
        // TODO: Create actual LLVM function type and add to module
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
