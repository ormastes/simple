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
    /// Import map: raw function name → mangled name for cross-module resolution
    pub(super) import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Per-module use map from `use` statements
    pub(super) use_map: std::collections::HashMap<String, String>,
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
            Err(crate::error::factory::llvm_feature_required())
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
                import_map: std::sync::Arc::new(std::collections::HashMap::new()),
                use_map: std::collections::HashMap::new(),
            })
        }
    }

    /// Set the import map for cross-module function resolution
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.import_map = map;
    }

    /// Set the per-module use map from `use` statements
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.use_map = map;
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
        Err(crate::error::factory::llvm_feature_not_enabled())
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
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

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
            _ => return Err(crate::error::factory::unsupported_return_type()),
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
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Declare a function with appropriate linkage.
    /// Functions with bodies get WeakAny linkage (like Cranelift's Preemptible) to avoid
    /// duplicate symbol errors in multi-file builds with --no-mangle.
    /// Functions without bodies (extern declarations) get External linkage.
    #[cfg(feature = "llvm")]
    pub fn declare_function_with_linkage(
        &self,
        name: &str,
        param_types: &[TypeId],
        return_type: &TypeId,
        has_body: bool,
    ) -> Result<(), CompileError> {
        let func = self.create_function_signature(name, param_types, return_type)?;
        if has_body {
            // Module-qualified names (containing "__") use External linkage so they
            // override weak stubs.  Bare names use WeakAny to avoid duplicate-symbol
            // errors when the same bare name appears in multiple modules.
            // The linker uses --allow-multiple-definition to handle the rare case of
            // genuinely duplicated mangled names across modules.
            if name.contains("__") || name == "spl_main" {
                func.set_linkage(inkwell::module::Linkage::External);
            } else {
                func.set_linkage(inkwell::module::Linkage::WeakAny);
            }
        } else {
            func.set_linkage(inkwell::module::Linkage::External);
        }
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn declare_function_with_linkage(
        &self,
        _name: &str,
        _param_types: &[TypeId],
        _return_type: &TypeId,
        _has_body: bool,
    ) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Get LLVM IR as string (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;
        Ok(module.print_to_string().to_string())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Verify the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn verify(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        module
            .verify()
            .map_err(|e| crate::error::factory::llvm_verification_failed(&e))?;
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn verify(&self) -> Result<(), CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }

    /// Take ownership of the LLVM module (for JIT execution engine creation).
    #[cfg(feature = "llvm")]
    pub fn take_module(&self) -> Option<Module<'static>> {
        self.module.borrow_mut().take()
    }

    /// Emit object code from the module (feature-gated)
    #[cfg(feature = "llvm")]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // Initialize LLVM targets
        LlvmTarget::initialize_all(&InitializationConfig::default());

        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_module_not_created)?;

        // Get target triple
        let triple = self.get_target_triple();
        let target_triple = inkwell::targets::TargetTriple::create(&triple);

        // Get target from triple
        let target = LlvmTarget::from_triple(&target_triple)
            .map_err(|e| crate::error::factory::llvm_target_failed(&triple, &e))?;

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
            .ok_or_else(crate::error::factory::llvm_target_machine_failed)?;

        // Emit object file to memory buffer
        let buffer = target_machine
            .write_to_memory_buffer(module, FileType::Object)
            .map_err(|e| crate::error::factory::llvm_emit_failed("object file", &e))?;

        Ok(buffer.as_slice().to_vec())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn emit_object(&self, _module: &MirModule) -> Result<Vec<u8>, CompileError> {
        Err(crate::error::factory::llvm_feature_not_enabled())
    }
}

impl NativeBackend for LlvmBackend {
    fn target(&self) -> &Target {
        &self.target
    }

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        let module_name = module.name.as_deref().unwrap_or("module");
        self.create_module(module_name)?;

        // Pre-declare runtime functions with correct signatures.
        // This prevents compile_call from creating wrong declarations when
        // MIR calls a runtime function with a different number of arguments
        // (e.g., rt_array_new called with 0 args in MIR vs 1 arg actual).
        //
        // Skip functions that the LLVM backend declares manually with ptr types
        // (Cranelift uses i64 for everything, but LLVM distinguishes ptr from i64).
        #[cfg(feature = "llvm")]
        {
            let m = self.module.borrow();
            if let Some(m) = m.as_ref() {
                let i64_type = self.context.i64_type();

                for spec in crate::codegen::runtime_ffi::RUNTIME_FUNCS {
                    // Skip if already declared
                    if m.get_function(spec.name).is_some() {
                        continue;
                    }

                    // Only pre-declare functions with ALL i64 params and i64 return.
                    // MIR always uses i64 for all values (tagged-value ABI).
                    // Functions with i8/i32/f64 params would cause type mismatches
                    // when compile_call passes i64 args. Those functions will be
                    // declared on-demand by compile_call with matching arg types,
                    // and the indirect call path handles arity mismatches.
                    let all_i64_params = spec.params.iter().all(|ty| *ty == cranelift_codegen::ir::types::I64);
                    let i64_return = spec.returns.len() == 1 && spec.returns[0] == cranelift_codegen::ir::types::I64;
                    let void_return = spec.returns.is_empty();

                    // Only pre-declare functions with ALL i64 params and i64 return.
                    // Skip void-return functions — they may clash with user-defined
                    // functions that return values (e.g. debug_stubs.spl redefines
                    // rt_fault_* to return bool). The arity-mismatch path in
                    // compile_call handles void functions fine.
                    if !all_i64_params || !i64_return {
                        continue;
                    }

                    let params: Vec<inkwell::types::BasicMetadataTypeEnum> =
                        spec.params.iter().map(|_| i64_type.into()).collect();

                    let fn_type = i64_type.fn_type(&params, false);
                    let f = m.add_function(spec.name, fn_type, None);
                    f.set_linkage(inkwell::module::Linkage::External);
                }
            }
        }

        // First pass: forward-declare all function signatures
        // This is necessary so that functions can call each other regardless of compilation order
        for func in &module.functions {
            let param_types: Vec<_> = func.params.iter().map(|p| p.ty).collect();
            self.declare_function_with_linkage(&func.name, &param_types, &func.return_type, !func.blocks.is_empty())?;
        }

        // Second pass: compile all function bodies
        for func in &module.functions {
            self.compile_function(func)?;
        }

        // Fix linkage after compilation:
        // 1. Declarations (no body) must have External linkage, not WeakAny.
        // 2. spl_main (entry point) must have Global linkage to beat the weak stub.
        #[cfg(feature = "llvm")]
        {
            let m = self.module.borrow();
            if let Some(m) = m.as_ref() {
                let mut func_opt = m.get_first_function();
                while let Some(f) = func_opt {
                    if f.count_basic_blocks() == 0 {
                        // No body — must be External
                        f.set_linkage(inkwell::module::Linkage::External);
                    } else if f.get_name().to_str() == Ok("spl_main") {
                        // Entry point must be a strong (Global) symbol so the linker
                        // prefers it over the weak spl_main in the C main stub.
                        f.set_linkage(inkwell::module::Linkage::External);
                    }
                    func_opt = f.get_next_function();
                }
            }
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
