//! Code generation, JIT compilation, and object file emission.

use simple_common::target::Target;

use super::core::CompilerPipeline;
use crate::codegen::{backend_trait::NativeBackend, BackendKind, Codegen};
use crate::codegen::llvm::LlvmBackend;
use crate::mir;
use crate::CompileError;

impl CompilerPipeline {
    pub(super) fn compile_mir_to_object(
        &self,
        mir_module: &mir::MirModule,
        target: Target,
    ) -> Result<Vec<u8>, CompileError> {
        if target.arch.is_32bit() && cfg!(not(feature = "llvm")) {
            return Err(CompileError::Codegen(
                "32-bit targets require the LLVM backend; build with --features llvm".to_string(),
            ));
        }

        // TODO: Re-enable coverage when module is complete
        // let coverage_enabled = crate::coverage::is_coverage_enabled();

        match BackendKind::for_target(&target) {
            BackendKind::Cranelift => {
                let codegen = Codegen::for_target(target)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))?;
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            BackendKind::Llvm => {
                let backend = LlvmBackend::new(target)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend
                    .with_coverage(false)  // TODO: Use coverage_enabled when module is complete
                    .compile(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
        }
    }
}
