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
}

impl BackendKind {
    /// Select the appropriate backend for a target
    #[allow(unused_variables)]
    pub fn for_target(target: &Target) -> Self {
        // Use LLVM for 32-bit targets if available, Cranelift for 64-bit
        #[cfg(feature = "llvm")]
        if target.arch.is_32bit() {
            return BackendKind::Llvm;
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
}
