//! AOT (Ahead-of-Time) compilation using Cranelift with ObjectModule.

use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::mir::MirModule;

use super::common_backend::{
    create_isa_and_flags, BackendError, BackendResult, BackendSettings, CodegenBackend,
};

// Re-export error types for backwards compatibility
pub use super::common_backend::BackendError as CodegenError;
pub type CodegenResult<T> = BackendResult<T>;

/// AOT Codegen context for translating MIR to object code
pub struct Codegen {
    backend: CodegenBackend<ObjectModule>,
}

impl Codegen {
    pub fn new() -> CodegenResult<Self> {
        let settings = BackendSettings::aot();
        let (_flags, isa) = create_isa_and_flags(&settings)?;

        let builder = ObjectBuilder::new(
            isa,
            "simple_module",
            cranelift_module::default_libcall_names(),
        )
        .map_err(|e| BackendError::ModuleError(e.to_string()))?;

        let module = ObjectModule::new(builder);
        let backend = CodegenBackend::with_module(module)?;

        Ok(Self { backend })
    }

    pub fn compile_module(mut self, mir: &MirModule) -> CodegenResult<Vec<u8>> {
        // Compile all functions
        self.backend.compile_all_functions(mir)?;

        // Emit object code
        let product = self.backend.module.finish();
        product
            .emit()
            .map_err(|e| BackendError::ModuleError(e.to_string()))
    }

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
