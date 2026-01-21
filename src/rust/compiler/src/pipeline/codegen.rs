//! Code generation, JIT compilation, and object file emission.

use simple_common::target::Target;

use super::core::CompilerPipeline;
use crate::codegen::llvm::LlvmBackend;
use crate::codegen::{backend_trait::NativeBackend, BackendKind, Codegen};
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

        // Coverage module is complete and available via SIMPLE_COVERAGE env var
        let coverage_enabled = crate::coverage::is_coverage_enabled();

        match BackendKind::for_target(&target) {
            BackendKind::Cranelift => {
                let codegen = Codegen::for_target(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            BackendKind::Llvm => {
                let backend = LlvmBackend::new(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend
                    .with_coverage(coverage_enabled)
                    .compile(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            #[cfg(feature = "vulkan")]
            BackendKind::Vulkan => {
                use crate::codegen::vulkan::VulkanBackend;
                let mut backend = VulkanBackend::new(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend.compile(mir_module)
            }
            BackendKind::Software => {
                // Software backend is for GPU kernel fallback, not general compilation
                Err(CompileError::Codegen(
                    "Software GPU backend cannot be used for general compilation; use for_gpu_kernel() instead"
                        .to_string(),
                ))
            }
        }
    }
}
