//! AOT (Ahead-of-Time) compilation using Cranelift with ObjectModule.

use cranelift_object::{ObjectBuilder, ObjectModule};

use simple_common::target::Target;

use crate::mir::MirModule;

use super::common_backend::{create_isa_and_flags, BackendError, BackendResult, BackendSettings, CodegenBackend};

// Re-export error types for backwards compatibility
pub use super::common_backend::BackendError as CodegenError;
pub type CodegenResult<T> = BackendResult<T>;

/// AOT Codegen context for translating MIR to object code
pub struct Codegen {
    backend: CodegenBackend<ObjectModule>,
}

impl Codegen {
    /// Create a new codegen for the host target.
    pub fn new() -> CodegenResult<Self> {
        Self::for_target(Target::host())
    }

    /// Create a new codegen for a specific target.
    ///
    /// This enables cross-compilation to different architectures.
    pub fn for_target(target: Target) -> CodegenResult<Self> {
        let settings = BackendSettings::aot_for_target(target);
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let builder = ObjectBuilder::new(isa, "simple_module", cranelift_module::default_libcall_names())
            .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        let module = ObjectModule::new(builder);
        let backend = CodegenBackend::with_module_and_target(module, target)?;

        Ok(Self { backend })
    }

    /// Get the target this codegen is compiling for.
    pub fn target(&self) -> &Target {
        self.backend.target()
    }

    /// Set the module prefix for name mangling in multi-file builds.
    pub fn set_module_prefix(&mut self, prefix: String) {
        self.backend.set_module_prefix(prefix);
    }

    /// Mark this module as the program entry point.
    ///
    /// When `true`, the `main` function is emitted as `spl_main` with
    /// Preemptible linkage. Non-entry modules mangle `main` like any
    /// other local function to avoid symbol collisions.
    pub fn set_entry_module(&mut self, is_entry: bool) {
        self.backend.set_entry_module(is_entry);
    }

    /// Set the import map for cross-module function resolution.
    pub fn set_import_map(&mut self, map: std::sync::Arc<std::collections::HashMap<String, String>>) {
        self.backend.set_import_map(map);
    }

    /// Set the ambiguous names for symbol resolution.
    pub fn set_ambiguous_names(&mut self, names: std::sync::Arc<std::collections::HashSet<String>>) {
        self.backend.set_ambiguous_names(names);
    }

    /// Set the per-module use map for resolving imports from `use` statements.
    pub fn set_use_map(&mut self, map: std::collections::HashMap<String, String>) {
        self.backend.set_use_map(map);
    }

    /// Compile a MIR module to object code.
    pub fn compile_module(mut self, mir: &MirModule) -> CodegenResult<Vec<u8>> {
        // Compile all functions
        self.backend.compile_all_functions(mir)?;

        // Emit object code
        let product = self.backend.module.finish();
        product.emit().map_err(|e| BackendError::ModuleError(e.to_string()))
    }

    /// Finish compilation and get the raw object code.
    pub fn get_object_code(self) -> Vec<u8> {
        let product = self.backend.module.finish();
        product.emit().unwrap()
    }
}

impl Default for Codegen {
    fn default() -> Self {
        Self::new().expect("Failed to create codegen")
    }
}

#[cfg(test)]
#[path = "cranelift_tests.rs"]
mod tests;
