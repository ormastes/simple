//! Common backend infrastructure for both AOT and JIT compilation.
//!
//! This module provides a generic `CodegenBackend<M: Module>` that handles
//! shared functionality between AOT (ObjectModule) and JIT (JITModule) backends.

use std::collections::HashMap;

use cranelift_codegen::ir::UserFuncName;
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
            is_pic: false,
            target: Target::host(),
        }
    }

    /// Settings for AOT compilation with a specific target
    pub fn aot_for_target(target: Target) -> Self {
        Self {
            opt_level: "speed",
            is_pic: false,
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
            body_stub: None,
            target,
        })
    }

    /// Get the target this backend is compiling for
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Declare external runtime functions for FFI using shared specifications.
    pub fn declare_runtime_functions(
        module: &mut M,
    ) -> BackendResult<HashMap<&'static str, cranelift_module::FuncId>> {
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
        let func_id = create_body_stub(&mut self.module, &mut ctx, "__simple_body_stub")
            .map_err(BackendError::ModuleError)?;

        self.body_stub = Some(func_id);
        Ok(func_id)
    }

    /// Declare all functions from a MIR module
    pub fn declare_functions(&mut self, functions: &[MirFunction]) -> BackendResult<()> {
        self.func_ids = super::shared::declare_functions(&mut self.module, functions)
            .map_err(BackendError::ModuleError)?;
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
        )
        .map_err(BackendError::ModuleError)?;

        // Verify the function before defining
        if let Err(errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            return Err(BackendError::ModuleError(format!(
                "Verifier errors:\n{}",
                errors
            )));
        }

        // Define the function
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| BackendError::ModuleError(format!("Compilation error: {}", e)))?;

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    /// Compile all functions from a MIR module (with outlining expansion)
    pub fn compile_all_functions(&mut self, mir: &MirModule) -> BackendResult<Vec<MirFunction>> {
        // Expand with outlined functions for body_block users
        let functions = expand_with_outlined(mir);

        // First pass: declare all functions
        self.declare_functions(&functions)?;

        // Second pass: compile function bodies
        for func in &functions {
            self.compile_function(func)?;
        }

        Ok(functions)
    }
}
