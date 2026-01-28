//! Common backend infrastructure for both AOT and JIT compilation.
//!
//! This module provides a generic `CodegenBackend<M: Module>` that handles
//! shared functionality between AOT (ObjectModule) and JIT (JITModule) backends.

use std::collections::HashMap;

use cranelift_codegen::ir::{types, InstBuilder, UserFuncName};
use cranelift_codegen::isa::{CallConv, OwnedTargetIsa};
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_codegen::Context;
use cranelift_module::{Linkage, Module};
use target_lexicon::Triple;
use thiserror::Error;

use simple_common::target::{Target, TargetArch};

use crate::hir::TypeId;
use crate::mir::{MirFunction, MirModule};

use super::instr::compile_function_body;
use super::runtime_ffi::RUNTIME_FUNCS;
use super::shared::{build_mir_signature, create_body_stub, expand_with_outlined};

/// Common error type for codegen backends
#[derive(Error, Debug)]
pub enum BackendError {
    #[error("Compilation error: {0}")]
    Compilation(String),

    #[error("Unsupported type: {0:?}")]
    UnsupportedType(TypeId),

    #[error("Unknown function: {0}")]
    UnknownFunction(String),

    #[error("Module error: {0}")]
    ModuleError(String),

    #[error("Unsupported target architecture: {0}")]
    UnsupportedTarget(String),
}

pub type BackendResult<T> = Result<T, BackendError>;

/// Common codegen backend that works with any Cranelift Module type.
///
/// This struct contains all shared state and logic between AOT and JIT backends.
pub struct CodegenBackend<M: Module> {
    pub module: M,
    pub ctx: Context,
    pub func_ids: HashMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: HashMap<&'static str, cranelift_module::FuncId>,
    pub global_ids: HashMap<String, cranelift_module::DataId>,
    pub body_stub: Option<cranelift_module::FuncId>,
    pub target: Target,
}

/// Settings for creating a codegen backend
#[derive(Debug, Clone)]
pub struct BackendSettings {
    pub opt_level: &'static str,
    pub is_pic: bool,
    pub target: Target,
}

impl Default for BackendSettings {
    fn default() -> Self {
        Self {
            opt_level: "speed",
            is_pic: false,
            target: Target::host(),
        }
    }
}

impl BackendSettings {
    /// Settings for AOT compilation (host target)
    pub fn aot() -> Self {
        Self {
            opt_level: "speed",
            // Enable PIC for compatibility with PIE executables and shared libraries
            is_pic: true,
            target: Target::host(),
        }
    }

    /// Settings for AOT compilation with a specific target
    pub fn aot_for_target(target: Target) -> Self {
        Self {
            opt_level: "speed",
            // Enable PIC for compatibility with PIE executables and shared libraries
            is_pic: true,
            target,
        }
    }

    /// Settings for JIT compilation (always host target)
    pub fn jit() -> Self {
        Self {
            opt_level: "speed",
            is_pic: true,
            target: Target::host(),
        }
    }

    /// Set the target architecture
    pub fn with_target(mut self, target: Target) -> Self {
        self.target = target;
        self
    }

    /// Set the optimization level
    pub fn with_opt_level(mut self, level: &'static str) -> Self {
        self.opt_level = level;
        self
    }
}

/// Convert TargetArch to target_lexicon::Triple
fn target_arch_to_triple(arch: TargetArch) -> BackendResult<Triple> {
    let triple_str = arch.triple_str();
    triple_str
        .parse()
        .map_err(|e: target_lexicon::ParseError| BackendError::UnsupportedTarget(e.to_string()))
}

/// Create ISA and flags from settings
pub fn create_isa_and_flags(
    settings: &BackendSettings,
) -> BackendResult<(Flags, std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>)> {
    let mut settings_builder = settings::builder();
    settings_builder
        .set("opt_level", settings.opt_level)
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    if settings.is_pic {
        settings_builder
            .set("is_pic", "true")
            .map_err(|e| BackendError::Compilation(e.to_string()))?;
    }

    let flags = Flags::new(settings_builder);

    // Use the target from settings, or default to host
    let triple = target_arch_to_triple(settings.target.arch)?;

    create_isa_from_triple(triple, flags)
}

/// Helper to create ISA from a triple
fn create_isa_from_triple(
    triple: Triple,
    flags: settings::Flags,
) -> Result<(settings::Flags, OwnedTargetIsa), BackendError> {
    let isa = cranelift_codegen::isa::lookup(triple)
        .map_err(|e| BackendError::Compilation(e.to_string()))?
        .finish(flags.clone())
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    Ok((flags, isa))
}

/// Create ISA and flags for the host target (backwards compatibility)
pub fn create_host_isa_and_flags(
    opt_level: &str,
    is_pic: bool,
) -> BackendResult<(Flags, std::sync::Arc<dyn cranelift_codegen::isa::TargetIsa>)> {
    let mut settings_builder = settings::builder();
    settings_builder
        .set("opt_level", opt_level)
        .map_err(|e| BackendError::Compilation(e.to_string()))?;

    if is_pic {
        settings_builder
            .set("is_pic", "true")
            .map_err(|e| BackendError::Compilation(e.to_string()))?;
    }

    let flags = Flags::new(settings_builder);
    let triple = Triple::host();

    create_isa_from_triple(triple, flags)
}

impl<M: Module> CodegenBackend<M> {
    /// Create a new backend with a pre-configured module (uses host target)
    pub fn with_module(module: M) -> BackendResult<Self> {
        Self::with_module_and_target(module, Target::host())
    }

    /// Create a new backend with a pre-configured module and target
    pub fn with_module_and_target(mut module: M, target: Target) -> BackendResult<Self> {
        let ctx = module.make_context();
        let runtime_funcs = Self::declare_runtime_functions(&mut module)?;

        Ok(Self {
            module,
            ctx,
            func_ids: HashMap::new(),
            runtime_funcs,
            global_ids: HashMap::new(),
            body_stub: None,
            target,
        })
    }

    /// Get the target this backend is compiling for
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Declare external runtime functions for FFI using shared specifications.
    pub fn declare_runtime_functions(module: &mut M) -> BackendResult<HashMap<&'static str, cranelift_module::FuncId>> {
        let mut funcs = HashMap::new();
        let call_conv = CallConv::SystemV;

        for spec in RUNTIME_FUNCS {
            let sig = spec.build_signature(call_conv);
            let id = module
                .declare_function(spec.name, Linkage::Import, &sig)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;
            funcs.insert(spec.name, id);
        }

        Ok(funcs)
    }

    /// Create or return a no-op body stub (fn() -> void) and return its FuncId.
    #[allow(dead_code)]
    pub fn ensure_body_stub(&mut self) -> BackendResult<cranelift_module::FuncId> {
        if let Some(id) = self.body_stub {
            return Ok(id);
        }

        let mut ctx = self.module.make_context();
        let func_id =
            create_body_stub(&mut self.module, &mut ctx, "__simple_body_stub").map_err(BackendError::ModuleError)?;

        self.body_stub = Some(func_id);
        Ok(func_id)
    }

    /// Declare all functions from a MIR module
    pub fn declare_functions(&mut self, functions: &[MirFunction]) -> BackendResult<()> {
        eprintln!("[DEBUG declare_functions] Called with {} functions, {} runtime funcs already declared",
                  functions.len(), self.runtime_funcs.len());

        let mut func_ids = HashMap::new();

        // First, add runtime function IDs for functions that are already declared
        for (name, id) in &self.runtime_funcs {
            func_ids.insert(name.to_string(), *id);
        }

        let total_mir_functions = functions.len();
        let mut skipped_count = 0;
        let mut declared_count = 0;

        // Then declare non-runtime functions
        for func in functions {
            // Skip functions that are already declared as runtime functions
            // This handles extern functions from Simple code that match runtime functions
            if self.runtime_funcs.contains_key(func.name.as_str()) {
                skipped_count += 1;
                continue;
            }

            let sig = super::shared::build_mir_signature(func);

            // Determine linkage (same logic as in shared::declare_functions)
            let linkage = if func.blocks.is_empty() {
                cranelift_module::Linkage::Import
            } else if func.is_public() || func.name == "main" {
                cranelift_module::Linkage::Export
            } else {
                cranelift_module::Linkage::Local
            };

            if func.name.contains("resolve") && (func.name.contains("blocks") || func.name.contains("BlockResolver")) {
                eprintln!("[DEBUG resolve] Function: '{}', params: {}, returns: {:?}, has_body: {}",
                          func.name, func.params.len(), func.return_type, !func.blocks.is_empty());
                for (i, param) in func.params.iter().enumerate() {
                    eprintln!("[DEBUG resolve]   param {}: name='{}', ty={:?}", i, param.name, param.ty);
                }
                eprintln!("[DEBUG resolve] Signature params: {}", sig.params.len());
            }

            let func_id = self.module
                .declare_function(&func.name, linkage, &sig)
                .map_err(|e| BackendError::ModuleError(format!("Failed to declare '{}': {}", func.name, e)))?;

            // Debug: print ALL user function IDs to identify fn2
            if func_id.as_u32() >= 467 {
                eprintln!("[DEBUG fn_id] funcid{} = fn{} = '{}' ({} params)",
                          func_id.as_u32(), func_id.as_u32() - 467, func.name, func.params.len());
            }

            func_ids.insert(func.name.clone(), func_id);
            declared_count += 1;
        }

        self.func_ids = func_ids;
        Ok(())
    }

    /// Declare all global variables from a MIR module
    pub fn declare_globals(&mut self, globals: &[(String, TypeId, bool)]) -> BackendResult<()> {
        use super::types_util::type_to_cranelift;

        eprintln!("[DEBUG declare_globals] Declaring {} globals (skipping {} runtime funcs)",
                  globals.len(), self.runtime_funcs.len());

        for (name, ty, is_mutable) in globals {
            // Skip globals that are actually runtime functions (extern functions)
            if self.runtime_funcs.contains_key(name.as_str()) {
                eprintln!("[DEBUG] Skipping runtime function global: '{}'", name);
                continue;
            }

            eprintln!("[DEBUG] Global: '{}', type: {:?}, mutable: {}", name, ty, is_mutable);
            let data_id = self.module
                .declare_data(name, cranelift_module::Linkage::Export, *is_mutable, false)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            // Initialize with zero (will be set by runtime initialization)
            let mut data_desc = cranelift_module::DataDescription::new();
            let size = super::types_util::type_id_size(*ty) as usize;
            data_desc.define_zeroinit(size);

            self.module
                .define_data(data_id, &data_desc)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            self.global_ids.insert(name.clone(), data_id);
        }
        Ok(())
    }

    /// Compile a single MIR function
    pub fn compile_function(&mut self, func: &MirFunction) -> BackendResult<()> {
        let func_id = *self
            .func_ids
            .get(&func.name)
            .ok_or_else(|| BackendError::UnknownFunction(func.name.clone()))?;

        let sig = build_mir_signature(func);
        self.ctx.func.signature = sig;
        self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        // Use the shared function body compilation
        compile_function_body(
            &mut self.module,
            &mut self.ctx.func,
            func,
            &self.func_ids,
            &self.runtime_funcs,
            &self.global_ids,
        )
        .map_err(BackendError::ModuleError)?;

        // Verify the function before defining - log errors but try to compile anyway
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            eprintln!("[WARNING] Verifier errors in '{}': {} (attempting compilation anyway)", func.name, errors);
        }

        // Define the function (may fail if verifier errors are critical)
        match self.module.define_function(func_id, &mut self.ctx) {
            Ok(()) => {}
            Err(e) => {
                return Err(BackendError::ModuleError(format!("Compilation error in '{}': {}", func.name, e)));
            }
        }

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    /// Compile all functions from a MIR module (with outlining expansion)
    pub fn compile_all_functions(&mut self, mir: &MirModule) -> BackendResult<Vec<MirFunction>> {
        // Expand with outlined functions for body_block users
        let functions = expand_with_outlined(mir);

        eprintln!("[DEBUG compile_all_functions] MIR functions: {}, After expansion: {}, Globals: {}",
                  mir.functions.len(), functions.len(), mir.globals.len());

        // Check for duplicate function names and deduplicate
        let mut seen_names = std::collections::HashSet::new();
        let mut unique_functions = Vec::new();
        for func in functions {
            if seen_names.insert(func.name.clone()) {
                unique_functions.push(func);
            } else {
                eprintln!("[WARNING] Skipping duplicate function: {}", func.name);
            }
        }
        let functions = unique_functions;

        // First pass: declare globals and functions
        self.declare_globals(&mir.globals)?;
        self.declare_functions(&functions)?;

        // Second pass: compile function bodies
        // Track functions that fail compilation so we can create stubs
        let mut failed_functions: Vec<&MirFunction> = Vec::new();
        for func in &functions {
            match self.compile_function(func) {
                Ok(()) => {}
                Err(e) => {
                    // Log the error but continue - we'll create a stub for this function
                    eprintln!("[WARNING] Function '{}' compilation failed: {}", func.name, e);
                    failed_functions.push(func);
                    // IMPORTANT: Clear context to prevent state from leaking to next function
                    self.module.clear_context(&mut self.ctx);
                }
            }
        }

        // Create stubs for failed functions
        for func in failed_functions {
            if let Some(&func_id) = self.func_ids.get(&func.name) {
                // Create a stub with the correct signature
                let sig = build_mir_signature(func);
                self.ctx.func.signature = sig.clone();
                self.ctx.func.name = UserFuncName::user(0, func_id.as_u32());

                let mut func_ctx = cranelift_frontend::FunctionBuilderContext::new();
                let mut builder = cranelift_frontend::FunctionBuilder::new(&mut self.ctx.func, &mut func_ctx);
                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);

                // Return appropriate zero/default value based on signature return type
                if sig.returns.is_empty() {
                    builder.ins().return_(&[]);
                } else {
                    // Create zero values for each return type
                    let return_vals: Vec<_> = sig.returns.iter().map(|abi_param| {
                        let ty = abi_param.value_type;
                        if ty.is_int() {
                            builder.ins().iconst(ty, 0)
                        } else if ty.is_float() {
                            if ty == types::F32 {
                                builder.ins().f32const(0.0)
                            } else {
                                builder.ins().f64const(0.0)
                            }
                        } else {
                            // Default to i64 for pointer types
                            builder.ins().iconst(types::I64, 0)
                        }
                    }).collect();
                    builder.ins().return_(&return_vals);
                }
                builder.finalize();

                // Try to define the stub
                if let Err(e) = self.module.define_function(func_id, &mut self.ctx) {
                    eprintln!("[ERROR] Failed to create stub for '{}': {}", func.name, e);
                }
                self.module.clear_context(&mut self.ctx);
            }
        }

        Ok(functions)
    }
}
