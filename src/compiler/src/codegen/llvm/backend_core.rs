/// LLVM backend core - struct definition, constructors, and basic accessors
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
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target as LlvmTarget, TargetMachine};
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;
#[cfg(feature = "llvm")]
use inkwell::values::FunctionValue;
#[cfg(feature = "llvm")]
use inkwell::OptimizationLevel;
#[cfg(feature = "llvm")]
use std::cell::RefCell;

/// LLVM-based code generator
pub struct LlvmBackend {
    pub(super) target: Target,
    /// Enable coverage instrumentation
    pub(super) coverage_enabled: bool,
    #[cfg(feature = "llvm")]
    pub(super) context: &'static Context,
    #[cfg(feature = "llvm")]
    pub(super) module: RefCell<Option<Module<'static>>>,
    #[cfg(feature = "llvm")]
    pub(super) builder: RefCell<Option<Builder<'static>>>,
    /// Counter for coverage basic blocks
    #[cfg(feature = "llvm")]
    pub(super) coverage_counter: RefCell<u32>,
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
        use simple_common::target::{TargetArch, TargetOS, WasmRuntime};

        let arch_str = match self.target.arch {
            TargetArch::X86_64 => "x86_64",
            TargetArch::Aarch64 => "aarch64",
            TargetArch::X86 => "i686",
            TargetArch::Arm => "armv7",
            TargetArch::Riscv64 => "riscv64",
            TargetArch::Riscv32 => "riscv32",
            TargetArch::Wasm32 => "wasm32",
            TargetArch::Wasm64 => "wasm64",
        };

        // WASM targets use runtime-specific triples
        if matches!(self.target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
            let runtime_str = match self.target.wasm_runtime {
                Some(WasmRuntime::Wasi) => "wasi",
                Some(WasmRuntime::Emscripten) => "unknown-emscripten",
                Some(WasmRuntime::Browser) | Some(WasmRuntime::Standalone) | None => "unknown-unknown",
            };
            return format!("{}-{}", arch_str, runtime_str);
        }

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
            TargetArch::X86 | TargetArch::Arm | TargetArch::Riscv32 | TargetArch::Wasm32 => 32,
            TargetArch::X86_64 | TargetArch::Aarch64 | TargetArch::Riscv64 | TargetArch::Wasm64 => 64,
        }
    }

    /// Create an LLVM module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn create_module(&self, name: &str) -> Result<(), CompileError> {
        use simple_common::target::{TargetArch, WasmRuntime};

        // Create module with the context
        let module = self.context.create_module(name);

        // Set target triple
        let triple = self.get_target_triple();
        module.set_triple(&inkwell::targets::TargetTriple::create(&triple));

        // Declare WASI imports for wasm32-wasi / wasm64-wasi targets
        if matches!(self.target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
            if matches!(self.target.wasm_runtime, Some(WasmRuntime::Wasi)) {
                #[cfg(feature = "wasm-wasi")]
                crate::codegen::llvm::wasm_imports::declare_wasi_imports(&module)?;
            }
        }

        *self.module.borrow_mut() = Some(module);

        // Create builder
        let builder = self.context.create_builder();
        *self.builder.borrow_mut() = Some(builder);

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
            _ => return Err(CompileError::Semantic("Unsupported return type".to_string())),
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
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
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
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
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
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
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
        let target = LlvmTarget::from_triple(&target_triple)
            .map_err(|e| CompileError::Semantic(format!("Failed to create target from triple: {}", e)))?;

        // Create target machine
        // For WASM targets, use static relocation mode (no PIC needed)
        let reloc_mode = if triple.contains("wasm") {
            RelocMode::Static
        } else {
            RelocMode::PIC
        };

        let target_machine = target
            .create_target_machine(
                &target_triple,
                "generic",
                "",
                OptimizationLevel::Default,
                reloc_mode,
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
        Err(CompileError::Semantic("LLVM feature not enabled".to_string()))
    }
}

impl NativeBackend for LlvmBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        let module_name = module.name.as_deref().unwrap_or("module");
        self.create_module(module_name)?;

        // First pass: forward-declare all function signatures
        // This is necessary so that functions can call each other regardless of compilation order
        for func in &module.functions {
            let param_types: Vec<_> = func.params.iter().map(|p| p.ty).collect();
            self.create_function_signature(&func.name, &param_types, &func.return_type)?;
        }

        // Second pass: compile all function bodies
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
        // LLVM supports all targets including WASM
        use simple_common::target::TargetArch;
        matches!(
            target.arch,
            TargetArch::X86_64
                | TargetArch::Aarch64
                | TargetArch::X86
                | TargetArch::Arm
                | TargetArch::Riscv64
                | TargetArch::Riscv32
                | TargetArch::Wasm32
                | TargetArch::Wasm64
        )
    }
}
