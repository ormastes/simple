/// Backend trait for code generation
///
/// This trait provides a unified interface for different code generation backends
/// (Cranelift, LLVM) to allow the compiler pipeline to be backend-agnostic.
use crate::error::CompileError;
use crate::mir::MirModule;
use simple_common::target::Target;

/// Native code generation backend
pub trait NativeBackend {
    /// Get the target architecture for this backend
    fn target(&self) -> &Target;

    /// Compile a MIR module to object code
    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError>;

    /// Get the name of this backend (for debugging/logging)
    fn name(&self) -> &'static str;

    /// Check if this backend supports the given target
    fn supports_target(target: &Target) -> bool
    where
        Self: Sized;
}

/// Backend selection based on target architecture
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackendKind {
    /// Cranelift backend (fast compilation, 64-bit only)
    Cranelift,
    /// LLVM backend (broader target support, including 32-bit)
    Llvm,
    /// Vulkan backend (GPU kernel compilation via SPIR-V)
    #[cfg(feature = "vulkan")]
    Vulkan,
    /// Software GPU backend (CPU fallback for GPU kernels)
    Software,
}

impl BackendKind {
    /// Select the appropriate backend for a target
    #[allow(unused_variables)]
    pub fn for_target(target: &Target) -> Self {
        #[cfg(feature = "llvm")]
        {
            use simple_common::target::TargetArch;

            // WASM always requires LLVM (Cranelift doesn't support WASM)
            if matches!(target.arch, TargetArch::Wasm32 | TargetArch::Wasm64) {
                return BackendKind::Llvm;
            }

            // Use LLVM for other 32-bit targets if available
            if target.arch.is_32bit() {
                return BackendKind::Llvm;
            }
        }

        // Default to Cranelift (available for all targets)
        BackendKind::Cranelift
    }

    /// Force a specific backend (for testing or user preference)
    pub fn force_cranelift() -> Self {
        BackendKind::Cranelift
    }

    /// Force LLVM backend
    pub fn force_llvm() -> Self {
        BackendKind::Llvm
    }

    /// Select the appropriate backend for GPU kernel compilation
    ///
    /// Returns Vulkan backend if available, otherwise falls back to Software backend
    /// which executes GPU kernels on the CPU.
    #[allow(unused_variables)]
    pub fn for_gpu_kernel(target: &Target) -> Self {
        #[cfg(feature = "vulkan")]
        {
            use crate::codegen::vulkan::VulkanBackend;

            if VulkanBackend::supports_target(target) {
                tracing::debug!("GPU kernel: Using Vulkan backend");
                return BackendKind::Vulkan;
            } else {
                tracing::warn!("Vulkan unavailable or unsupported, using software GPU backend");
            }
        }

        #[cfg(not(feature = "vulkan"))]
        {
            tracing::info!("Vulkan feature disabled, using software GPU backend");
        }

        BackendKind::Software
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_common::target::{TargetArch, TargetOS};

    #[test]
    fn test_backend_selection_32bit() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = BackendKind::for_target(&target);
        #[cfg(feature = "llvm")]
        assert!(matches!(backend, BackendKind::Llvm));
        #[cfg(not(feature = "llvm"))]
        assert!(matches!(backend, BackendKind::Cranelift));
    }

    #[test]
    fn test_backend_selection_64bit() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = BackendKind::for_target(&target);
        assert!(matches!(backend, BackendKind::Cranelift));
    }

    #[test]
    fn test_force_backends() {
        let cranelift = BackendKind::force_cranelift();
        assert!(matches!(cranelift, BackendKind::Cranelift));

        let llvm = BackendKind::force_llvm();
        assert!(matches!(llvm, BackendKind::Llvm));
    }

    // =============================================================================
    // GPU Kernel Backend Selection Tests
    // =============================================================================

    #[test]
    #[cfg(feature = "vulkan")]
    fn test_for_gpu_kernel_returns_vulkan_or_software() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = BackendKind::for_gpu_kernel(&target);

        // Should only return Vulkan or Software, never Cranelift or LLVM
        match backend {
            BackendKind::Vulkan | BackendKind::Software => {
                // Expected
            }
            _ => panic!(
                "for_gpu_kernel should only return Vulkan or Software, got {:?}",
                backend
            ),
        }
    }

    #[test]
    #[cfg(not(feature = "vulkan"))]
    fn test_for_gpu_kernel_without_vulkan_feature() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = BackendKind::for_gpu_kernel(&target);

        // Without vulkan feature, should always return Software
        assert_eq!(
            backend,
            BackendKind::Software,
            "for_gpu_kernel should return Software when vulkan feature disabled"
        );
    }

    #[test]
    fn test_for_gpu_kernel_x86_64() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = BackendKind::for_gpu_kernel(&target);

        // Verify it's one of the expected backends
        #[cfg(feature = "vulkan")]
        assert!(
            matches!(backend, BackendKind::Software) || matches!(backend, BackendKind::Vulkan),
            "Unexpected backend for X86_64: {:?}",
            backend
        );
        #[cfg(not(feature = "vulkan"))]
        assert!(
            matches!(backend, BackendKind::Software),
            "Unexpected backend for X86_64: {:?}",
            backend
        );
    }

    #[test]
    fn test_for_gpu_kernel_aarch64() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::Linux);
        let backend = BackendKind::for_gpu_kernel(&target);

        // Should work on ARM64 too (Vulkan is cross-platform)
        #[cfg(feature = "vulkan")]
        assert!(
            matches!(backend, BackendKind::Software) || matches!(backend, BackendKind::Vulkan),
            "Unexpected backend for ARM64: {:?}",
            backend
        );
        #[cfg(not(feature = "vulkan"))]
        assert!(
            matches!(backend, BackendKind::Software),
            "Unexpected backend for ARM64: {:?}",
            backend
        );
    }

    #[test]
    fn test_for_gpu_kernel_consistency() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);

        // Call multiple times, should get same result
        let backend1 = BackendKind::for_gpu_kernel(&target);
        let backend2 = BackendKind::for_gpu_kernel(&target);
        let backend3 = BackendKind::for_gpu_kernel(&target);

        assert_eq!(backend1, backend2, "for_gpu_kernel should be deterministic");
        assert_eq!(backend2, backend3, "for_gpu_kernel should be deterministic");
    }

    #[test]
    fn test_for_target_never_returns_software() {
        let targets = vec![
            Target::new(TargetArch::X86_64, TargetOS::Linux),
            Target::new(TargetArch::X86_64, TargetOS::Windows),
            Target::new(TargetArch::Aarch64, TargetOS::Linux),
            Target::new(TargetArch::X86, TargetOS::Linux),
        ];

        for target in targets {
            let backend = BackendKind::for_target(&target);
            assert_ne!(
                backend,
                BackendKind::Software,
                "for_target should never return Software backend for {:?}",
                target
            );
        }
    }

    #[test]
    #[cfg(feature = "vulkan")]
    fn test_for_target_never_returns_vulkan() {
        let targets = vec![
            Target::new(TargetArch::X86_64, TargetOS::Linux),
            Target::new(TargetArch::X86_64, TargetOS::Windows),
            Target::new(TargetArch::Aarch64, TargetOS::Linux),
        ];

        for target in targets {
            let backend = BackendKind::for_target(&target);
            assert_ne!(
                backend,
                BackendKind::Vulkan,
                "for_target should never return Vulkan backend for {:?}",
                target
            );
        }
    }

    // =============================================================================
    // Backend Kind Trait Tests
    // =============================================================================

    #[test]
    fn test_backend_kind_clone() {
        let backend = BackendKind::Cranelift;
        let cloned = backend.clone();
        assert_eq!(backend, cloned, "Clone should produce equal value");
    }

    #[test]
    fn test_backend_kind_copy() {
        let backend = BackendKind::Cranelift;
        let copied = backend; // Copy, not move
        assert_eq!(
            backend, copied,
            "Copy should produce equal value and not move"
        );
        // If Copy wasn't implemented, this line would fail:
        assert_eq!(backend, BackendKind::Cranelift);
    }

    #[test]
    fn test_backend_kind_equality() {
        // Test Eq implementation
        assert_eq!(BackendKind::Cranelift, BackendKind::Cranelift);
        assert_eq!(BackendKind::Llvm, BackendKind::Llvm);
        assert_eq!(BackendKind::Software, BackendKind::Software);

        assert_ne!(BackendKind::Cranelift, BackendKind::Llvm);
        assert_ne!(BackendKind::Cranelift, BackendKind::Software);
        assert_ne!(BackendKind::Llvm, BackendKind::Software);

        #[cfg(feature = "vulkan")]
        {
            assert_eq!(BackendKind::Vulkan, BackendKind::Vulkan);
            assert_ne!(BackendKind::Vulkan, BackendKind::Cranelift);
            assert_ne!(BackendKind::Vulkan, BackendKind::Llvm);
            assert_ne!(BackendKind::Vulkan, BackendKind::Software);
        }
    }

    #[test]
    fn test_backend_kind_debug() {
        // Test Debug implementation
        let cranelift = BackendKind::Cranelift;
        let debug_str = format!("{:?}", cranelift);
        assert!(
            debug_str.contains("Cranelift"),
            "Debug output should contain variant name"
        );

        let llvm = BackendKind::Llvm;
        let debug_str = format!("{:?}", llvm);
        assert!(
            debug_str.contains("Llvm"),
            "Debug output should contain variant name"
        );

        let software = BackendKind::Software;
        let debug_str = format!("{:?}", software);
        assert!(
            debug_str.contains("Software"),
            "Debug output should contain variant name"
        );

        #[cfg(feature = "vulkan")]
        {
            let vulkan = BackendKind::Vulkan;
            let debug_str = format!("{:?}", vulkan);
            assert!(
                debug_str.contains("Vulkan"),
                "Debug output should contain variant name"
            );
        }
    }

    #[test]
    fn test_backend_kind_partial_eq() {
        // Test PartialEq implementation (via assert_eq/assert_ne)
        assert!(BackendKind::Cranelift == BackendKind::Cranelift);
        assert!(BackendKind::Llvm == BackendKind::Llvm);
        assert!(BackendKind::Cranelift != BackendKind::Llvm);
    }
}
