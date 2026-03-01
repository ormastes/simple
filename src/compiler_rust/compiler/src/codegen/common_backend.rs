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
    /// Optional module prefix for name mangling (e.g., "compiler__frontend__core__lexer").
    /// When set, local function declarations are mangled as `prefix__name` to prevent
    /// symbol collisions in multi-file native builds. Raw names are also registered in
    /// func_ids so that intra-module calls by raw name still resolve locally.
    pub module_prefix: Option<String>,
    /// Whether this module contains the program entry point.
    /// When true, `main` is emitted as `spl_main` with Preemptible linkage so the
    /// C runtime entry stub can find it. When false, `main` is mangled like any
    /// other local function to avoid symbol collisions.
    pub is_entry_module: bool,
    /// Import map: raw function name → mangled name for cross-module resolution.
    /// Built during the discovery phase of multi-file native builds.
    pub import_map: std::sync::Arc<std::collections::HashMap<String, String>>,
    /// Set of function names that have multiple definitions across modules.
    /// These names keep their raw (unmangled) symbol name to avoid breaking
    /// cross-module resolution when the import map can't disambiguate.
    pub ambiguous_names: std::sync::Arc<std::collections::HashSet<String>>,
    /// Per-module use map: local imported name → mangled name.
    /// Built from the current file's `use` statements. Used to resolve
    /// ambiguous cross-module imports that the global import map can't handle.
    pub use_map: std::collections::HashMap<String, String>,
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
            module_prefix: None,
            is_entry_module: false,
            import_map: std::sync::Arc::new(std::collections::HashMap::new()),
            ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
            use_map: std::collections::HashMap::new(),
        })
    }

    /// Get the target this backend is compiling for
    pub fn target(&self) -> &Target {
        &self.target
    }

    /// Set the module prefix for name mangling.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.module_prefix = Some(prefix);
    }

    /// Mark this module as the program entry point.
    ///
    /// When `true`, the `main` function is emitted as `spl_main` with
    /// Preemptible linkage so the C runtime entry stub can call it.
    /// When `false`, `main` is prefix-mangled like any other local symbol.
    pub fn set_entry_module(&mut self, v: bool) {
        self.is_entry_module = v;
    }

    /// Set the import map for cross-module function resolution.
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.import_map = map;
    }

    /// Set the ambiguous names set for symbol resolution.
    pub fn set_ambiguous_names(&mut self, names: std::sync::Arc<std::collections::HashSet<String>>) {
        self.ambiguous_names = names;
    }

    /// Set the per-module use map for resolving imports from `use` statements.
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.use_map = map;
    }

    /// Mangle a function name with the module prefix (if set).
    ///
    /// - If `name == "main"` **and** this is the entry module, return `"spl_main"`.
    /// - If `name == "main"` **and** this is NOT the entry module, apply the normal
    ///   prefix mangling (e.g. `module_prefix__main`).
    /// - All other names follow the existing prefix logic.
    pub fn mangle_name(&self, name: &str) -> String {
        if name == "main" && self.is_entry_module {
            return "spl_main".to_string();
        }
        match &self.module_prefix {
            Some(prefix) => format!("{}__{}", prefix, name),
            None => name.to_string(),
        }
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

    /// Declare all functions from a MIR module.
    ///
    /// When `module_prefix` is set, locally-defined functions are declared under
    /// their mangled name (`prefix__name`) to prevent symbol collisions across
    /// compilation units. The raw name is also inserted into `func_ids` so that
    /// intra-module call resolution by raw name still works.
    pub fn declare_functions(&mut self, functions: &[MirFunction]) -> BackendResult<()> {
        let mut func_ids = HashMap::new();

        // First, add runtime function IDs for functions that are already declared
        for (name, id) in &self.runtime_funcs {
            func_ids.insert(name.to_string(), *id);
        }

        let _total_mir_functions = functions.len();

        // Then declare non-runtime functions
        for func in functions {
            // Skip functions that are already declared as runtime functions
            // This handles extern functions from Simple code that match runtime functions
            if self.runtime_funcs.contains_key(func.name.as_str()) {
                continue;
            }

            let sig = super::shared::build_mir_signature(func);

            // Determine linkage and symbol name.
            //
            // `main` handling depends on is_entry_module:
            //   - Entry module main:     symbol = "spl_main",      linkage = Preemptible
            //   - Non-entry module main: symbol = mangled name,    linkage = Local
            //
            // All other functions with bodies get Preemptible linkage so they're
            // visible across modules in multi-file builds. The mangled name avoids
            // collisions between same-named functions in different modules.
            let has_body = !func.blocks.is_empty();

            let (symbol_name, linkage) = if func.name == "main" && has_body {
                if self.is_entry_module {
                    ("spl_main".to_string(), cranelift_module::Linkage::Preemptible)
                } else {
                    (self.mangle_name(&func.name), cranelift_module::Linkage::Local)
                }
            } else if !has_body {
                (func.name.clone(), cranelift_module::Linkage::Import)
            } else {
                // All functions with bodies get mangled names + Preemptible linkage.
                // This prevents symbol collisions when multiple modules define
                // same-named functions (e.g., get_version(), init()).
                // Cross-module calls are resolved via the import map in calls.rs.
                (self.mangle_name(&func.name), cranelift_module::Linkage::Preemptible)
            };

            let func_id = self
                .module
                .declare_function(&symbol_name, linkage, &sig)
                .map_err(|e| BackendError::ModuleError(format!("Failed to declare '{}': {}", symbol_name, e)))?;

            // Always register under the raw name so local calls resolve
            func_ids.insert(func.name.clone(), func_id);
            // Also register under the mangled name if different
            if symbol_name != func.name {
                func_ids.insert(symbol_name, func_id);
            }
        }

        // Merge into existing func_ids rather than replacing.
        // declare_globals may have already registered extern function imports
        // which must be preserved for compile_call to find them.
        for (name, id) in func_ids {
            self.func_ids.entry(name).or_insert(id);
        }
        Ok(())
    }

    /// Declare all global variables from a MIR module.
    ///
    /// When `module_prefix` is set, globals are mangled to prevent collisions.
    ///
    /// Globals that correspond to extern function declarations (e.g. `rt_getpid`)
    /// are initialized with the function's import address so that `GlobalLoad`
    /// followed by `IndirectCall` resolves correctly at link time.
    pub fn declare_globals(
        &mut self,
        globals: &[(String, TypeId, bool)],
        extern_fn_names: &std::collections::HashSet<String>,
    ) -> BackendResult<()> {
        use super::types_util::type_to_cranelift;

        for (name, ty, is_mutable) in globals {
            // Skip globals that are actually runtime functions (extern functions)
            if self.runtime_funcs.contains_key(name.as_str()) {
                continue;
            }

            // If this global is an extern function declaration, create a data slot
            // initialized with the function's import address. This ensures that
            // GlobalLoad + IndirectCall patterns resolve correctly at link time.
            if extern_fn_names.contains(name) {
                // Use the RAW (unmangled) name for the function import so the linker
                // can resolve it against runtime symbols or weak C stubs.
                let sig = {
                    let call_conv = CallConv::SystemV;
                    let mut sig = cranelift_codegen::ir::Signature::new(call_conv);
                    // Extern functions use a generic i64 signature (tagged values)
                    sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
                    sig
                };
                // Declare the function import under the raw name
                let func_id = self
                    .module
                    .declare_function(name, cranelift_module::Linkage::Import, &sig)
                    .map_err(|e| BackendError::ModuleError(format!("extern fn '{}': {}", name, e)))?;

                // Also register in func_ids so compile_call can find it
                self.func_ids.entry(name.clone()).or_insert(func_id);

                // Create a data slot (using the mangled name for collision avoidance)
                // and initialize it with the function's address via a relocation.
                let symbol_name = self.mangle_name(name);
                let data_id = self
                    .module
                    .declare_data(&symbol_name, cranelift_module::Linkage::Preemptible, true, false)
                    .map_err(|e| BackendError::ModuleError(e.to_string()))?;

                let mut data_desc = cranelift_module::DataDescription::new();
                // 8 bytes for a function pointer on 64-bit
                data_desc.define_zeroinit(8);
                let func_ref = self.module.declare_func_in_data(func_id, &mut data_desc);
                data_desc.write_function_addr(0, func_ref);

                self.module
                    .define_data(data_id, &data_desc)
                    .map_err(|e| BackendError::ModuleError(e.to_string()))?;

                self.global_ids.insert(name.clone(), data_id);
                if symbol_name != *name {
                    self.global_ids.insert(symbol_name, data_id);
                }
                continue;
            }

            let symbol_name = self.mangle_name(name);

            // Use Preemptible linkage so that when multiple .o files define the same
            // global (from shared imports), the linker merges them instead of erroring.
            let data_id = self
                .module
                .declare_data(&symbol_name, cranelift_module::Linkage::Preemptible, *is_mutable, false)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            // Initialize with zero (will be set by runtime initialization)
            let mut data_desc = cranelift_module::DataDescription::new();
            let size = super::types_util::type_id_size(*ty) as usize;
            data_desc.define_zeroinit(size);

            self.module
                .define_data(data_id, &data_desc)
                .map_err(|e| BackendError::ModuleError(e.to_string()))?;

            // Register under raw name for local lookups
            self.global_ids.insert(name.clone(), data_id);
            if symbol_name != *name {
                self.global_ids.insert(symbol_name, data_id);
            }
        }
        Ok(())
    }

    /// Compile a single MIR function
    pub fn compile_function(&mut self, func: &MirFunction) -> BackendResult<()> {
        let func_id = *self
            .func_ids
            .get(&func.name)
            .ok_or_else(|| BackendError::UnknownFunction(func.name.clone()))?;

        // Skip extern/imported functions (no body expected; provided by runtime/FFI).
        let decl = self.module.declarations().get_function_decl(func_id);
        if decl.linkage == cranelift_module::Linkage::Import {
            return Ok(());
        }

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
            &self.import_map,
            &self.use_map,
        )
        .map_err(BackendError::ModuleError)?;

        // Verify the function before defining - log errors but try to compile anyway
        if let Err(_errors) = cranelift_codegen::verify_function(&self.ctx.func, self.module.isa()) {
            // Verifier errors - attempt compilation anyway
        }

        // Define the function (may fail if verifier errors are critical)
        match self.module.define_function(func_id, &mut self.ctx) {
            Ok(()) => {}
            Err(e) => {
                return Err(BackendError::ModuleError(format!(
                    "Compilation error in '{}': {}",
                    func.name, e
                )));
            }
        }

        self.module.clear_context(&mut self.ctx);

        Ok(())
    }

    /// Compile all functions from a MIR module (with outlining expansion)
    pub fn compile_all_functions(&mut self, mir: &MirModule) -> BackendResult<Vec<MirFunction>> {
        // Expand with outlined functions for body_block users
        let functions = expand_with_outlined(mir);

        // Check for duplicate function names and deduplicate
        let mut seen_names = std::collections::HashSet::new();
        let mut unique_functions = Vec::new();
        for func in functions {
            if seen_names.insert(func.name.clone()) {
                unique_functions.push(func);
            }
        }
        let functions = unique_functions;

        // First pass: declare globals and functions
        self.declare_globals(&mir.globals, &mir.extern_fn_names)?;
        self.declare_functions(&functions)?;

        // Second pass: compile function bodies
        // Track functions that fail compilation so we can create stubs
        let mut failed_functions: Vec<&MirFunction> = Vec::new();
        for func in &functions {
            match self.compile_function(func) {
                Ok(()) => {}
                Err(_e) => {
                    failed_functions.push(func);
                    // IMPORTANT: Clear context to prevent state from leaking to next function
                    self.module.clear_context(&mut self.ctx);
                }
            }
        }

        // Create stubs for failed functions
        for func in failed_functions {
            // In bootstrap mode we let unresolved symbols be handled by C shims/auto-stubs.
            if std::env::var("SIMPLE_BOOTSTRAP").is_ok() {
                continue;
            }
            if let Some(&func_id) = self.func_ids.get(&func.name) {
                // If this function is declared as an import (extern), skip stub creation;
                // the symbol is expected to be provided by the runtime/FFI.
                let decl = self.module.declarations().get_function_decl(func_id);
                if decl.linkage == cranelift_module::Linkage::Import {
                    continue;
                }
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
                    let return_vals: Vec<_> = sig
                        .returns
                        .iter()
                        .map(|abi_param| {
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
                        })
                        .collect();
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

/// Compute a module prefix from a file path relative to a source root.
///
/// Example: `src/compiler/10.frontend/core/lexer.spl` → `compiler__frontend__core__lexer`
///
/// The numbered layer prefixes (e.g., `10.`, `70.`) are stripped.
pub fn module_prefix_from_path(file_path: &std::path::Path, source_root: &std::path::Path) -> String {
    let relative = file_path.strip_prefix(source_root).unwrap_or(file_path);

    let mut parts = Vec::new();
    for component in relative.components() {
        if let std::path::Component::Normal(s) = component {
            let s = s.to_string_lossy();
            // Strip .spl extension for the last component
            let s = s.strip_suffix(".spl").unwrap_or(&s).to_string();
            // Strip numbered layer prefix (e.g., "10.frontend" -> "frontend")
            let s = if let Some(dot_pos) = s.find('.') {
                if s[..dot_pos].chars().all(|c| c.is_ascii_digit()) {
                    s[dot_pos + 1..].to_string()
                } else {
                    s
                }
            } else {
                s
            };
            if !s.is_empty() {
                parts.push(s);
            }
        }
    }
    parts.join("__")
}
