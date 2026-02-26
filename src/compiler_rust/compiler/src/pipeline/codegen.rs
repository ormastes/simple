//! Code generation, JIT compilation, and object file emission.

use simple_common::target::Target;
use std::env;

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
        let backend = select_backend(&target)?;

        match backend {
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
            BackendKind::CraneliftJit | BackendKind::LlvmJit | BackendKind::AutoJit => {
                // JIT backends are for in-process execution, not AOT compilation.
                // Fall back to Cranelift AOT for object code generation.
                let codegen = Codegen::for_target(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
        }
    }
}

fn select_backend(target: &Target) -> Result<BackendKind, CompileError> {
    let mut backend = BackendKind::for_target(target);

    // SIMPLE_FORCE_LLVM takes precedence over SIMPLE_BACKEND
    let force_llvm = env::var("SIMPLE_FORCE_LLVM")
        .map(|v| matches!(v.to_ascii_lowercase().as_str(), "1" | "true" | "yes" | "on"))
        .unwrap_or(false);

    if force_llvm {
        if cfg!(feature = "llvm") {
            backend = BackendKind::Llvm;
        } else {
            return Err(CompileError::Codegen(
                "SIMPLE_FORCE_LLVM is set but this build does not include the 'llvm' feature".to_string(),
            ));
        }
    }

    if let Ok(value) = env::var("SIMPLE_BACKEND") {
        let value = value.to_ascii_lowercase();
        backend = match value.as_str() {
            "auto" => BackendKind::for_target(target),
            "cranelift" => BackendKind::Cranelift,
            "llvm" => {
                if cfg!(feature = "llvm") {
                    BackendKind::Llvm
                } else {
                    return Err(CompileError::Codegen(
                        "SIMPLE_BACKEND=llvm but compiler was built without --features llvm".to_string(),
                    ));
                }
            }
            other => {
                return Err(CompileError::Codegen(format!(
                    "unknown SIMPLE_BACKEND '{}', expected auto|cranelift|llvm",
                    other
                )))
            }
        };
    }

    Ok(backend)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn backend_env_defaults_to_target_selection() {
        env::remove_var("SIMPLE_BACKEND");
        env::remove_var("SIMPLE_FORCE_LLVM");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::for_target(&target));
    }

    #[test]
    fn backend_env_respects_cranelift_override() {
        env::set_var("SIMPLE_BACKEND", "cranelift");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::Cranelift);
        env::remove_var("SIMPLE_BACKEND");
    }

    #[test]
    #[cfg(feature = "llvm")]
    fn backend_env_respects_llvm_override() {
        env::set_var("SIMPLE_BACKEND", "llvm");
        let target = Target::host();
        let backend = select_backend(&target).unwrap();
        assert_eq!(backend, BackendKind::Llvm);
        env::remove_var("SIMPLE_BACKEND");
    }

    #[test]
    fn backend_env_unknown_value_errors() {
        env::set_var("SIMPLE_BACKEND", "unknown-backend");
        let target = Target::host();
        let result = select_backend(&target);
        assert!(result.is_err());
        env::remove_var("SIMPLE_BACKEND");
    }
}
