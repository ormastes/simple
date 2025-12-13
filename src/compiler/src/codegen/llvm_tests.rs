/// LLVM backend tests
///
/// Tests for LLVM-based code generation supporting 32-bit and 64-bit targets.
/// This backend complements Cranelift by providing broader architecture support.

#[cfg(test)]
mod tests {
    use crate::codegen::backend_trait::NativeBackend;
    use crate::codegen::llvm::*;
    use simple_common::target::{Target, TargetArch, TargetOS};

    /// Test that LLVM backend can be created for 64-bit x86_64
    #[test]
    fn test_llvm_backend_create_x86_64() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit i686
    #[test]
    fn test_llvm_backend_create_i686() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit ARMv7
    #[test]
    fn test_llvm_backend_create_armv7() {
        let target = Target::new(TargetArch::Arm, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit RISC-V
    #[test]
    fn test_llvm_backend_create_riscv32() {
        let target = Target::new(TargetArch::Riscv32, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test LLVM type mapping for basic types
    #[test]
    fn test_llvm_type_mapping() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // Test integer types map correctly
        assert_eq!(backend.map_type(&T::I32).unwrap(), LlvmType::I32);
        assert_eq!(backend.map_type(&T::I64).unwrap(), LlvmType::I64);
        assert_eq!(backend.map_type(&T::U32).unwrap(), LlvmType::I32);
        assert_eq!(backend.map_type(&T::U64).unwrap(), LlvmType::I64);
        
        // Test floating point types
        assert_eq!(backend.map_type(&T::F32).unwrap(), LlvmType::F32);
        assert_eq!(backend.map_type(&T::F64).unwrap(), LlvmType::F64);
        
        // Test bool
        assert_eq!(backend.map_type(&T::BOOL).unwrap(), LlvmType::I1);
    }

    /// Test pointer width consistency
    #[test]
    fn test_pointer_width_32bit() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 32);
    }

    /// Test pointer width consistency for 64-bit
    #[test]
    fn test_pointer_width_64bit() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test simple function compilation (stub test - will be replaced with real MIR)
    #[test]
    fn test_compile_simple_function() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // TODO: Create proper MIR function when implementing actual compilation
        // For now, just verify the backend can be created
        assert_eq!(backend.name(), "llvm");
    }

    /// Test that backend can emit object code
    #[test]
    fn test_emit_object_code() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // TODO: Create proper MIR module when implementing object emission
        // For now, just verify backend supports the target
        assert!(LlvmBackend::supports_target(&target));
    }

    /// Test backend reports correct target
    #[test]
    fn test_backend_target() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        assert_eq!(backend.target().arch, TargetArch::X86);
        assert_eq!(backend.target().os, TargetOS::Linux);
    }

    /// Test that backend can handle multiple functions (stub test)
    #[test]
    fn test_compile_multiple_functions() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // TODO: Will implement when we have proper MIR function creation
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test NativeBackend trait implementation
    #[test]
    fn test_native_backend_trait() {
        use crate::codegen::backend_trait::NativeBackend;
        
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // Test trait methods
        assert_eq!(backend.name(), "llvm");
        assert_eq!(backend.target().arch, TargetArch::X86_64);
        
        // Test supports_target
        assert!(LlvmBackend::supports_target(&Target::new(TargetArch::X86, TargetOS::Linux)));
        assert!(LlvmBackend::supports_target(&Target::new(TargetArch::X86_64, TargetOS::Linux)));
        assert!(LlvmBackend::supports_target(&Target::new(TargetArch::Arm, TargetOS::Linux)));
        assert!(LlvmBackend::supports_target(&Target::new(TargetArch::Riscv32, TargetOS::Linux)));
        
        // TODO: Test compile through trait when we have proper MIR construction
    }
}
