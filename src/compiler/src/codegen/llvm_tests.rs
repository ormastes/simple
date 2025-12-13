/// LLVM backend tests
///
/// Tests for LLVM-based code generation supporting 32-bit and 64-bit targets.
/// This backend complements Cranelift by providing broader architecture support.
///
/// NOTE: Most tests require the `llvm` feature flag to be enabled.

#[cfg(test)]
mod tests {
    use crate::codegen::backend_trait::NativeBackend;
    use crate::codegen::llvm::*;
    use simple_common::target::{Target, TargetArch, TargetOS};

    /// Test that LLVM backend returns error without llvm feature
    #[test]
    #[cfg(not(feature = "llvm"))]
    fn test_llvm_backend_requires_feature() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_err());
        let err = backend.unwrap_err();
        assert!(err.to_string().contains("llvm") || err.to_string().contains("feature"));
    }

    /// Test that LLVM backend can be created for 64-bit x86_64
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_backend_create_x86_64() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit i686
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_backend_create_i686() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit ARMv7
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_backend_create_armv7() {
        let target = Target::new(TargetArch::Arm, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit RISC-V
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_backend_create_riscv32() {
        let target = Target::new(TargetArch::Riscv32, TargetOS::Linux);
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test LLVM type mapping for basic types
    #[test]
    #[cfg(feature = "llvm")]
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
    #[cfg(feature = "llvm")]
    fn test_pointer_width_32bit() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 32);
    }

    /// Test pointer width consistency for 64-bit
    #[test]
    #[cfg(feature = "llvm")]
    fn test_pointer_width_64bit() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test simple function compilation (stub test - will be replaced with real MIR)
    #[test]
    #[cfg(feature = "llvm")]
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
        
        // TODO: Create proper MIR module when implementing object emission
        // For now, just verify backend supports the target
        assert!(LlvmBackend::supports_target(&target));
    }

    /// Test backend reports correct target
    #[test]
    #[cfg(feature = "llvm")]
    fn test_backend_target() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        assert_eq!(backend.target().arch, TargetArch::X86);
        assert_eq!(backend.target().os, TargetOS::Linux);
    }

    /// Test that backend can handle multiple functions (stub test)
    #[test]
    #[cfg(feature = "llvm")]
    fn test_compile_multiple_functions() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // TODO: Will implement when we have proper MIR function creation
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test NativeBackend trait implementation
    #[test]
    #[cfg(feature = "llvm")]
    fn test_native_backend_trait() {
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

    /// Test backend selection logic (doesn't require llvm feature)
    #[test]
    fn test_backend_kind_selection() {
        use crate::codegen::BackendKind;
        
        // 32-bit targets should select LLVM
        let target_32 = Target::new(TargetArch::X86, TargetOS::Linux);
        assert!(matches!(BackendKind::for_target(&target_32), BackendKind::Llvm));
        
        // 64-bit targets should select Cranelift (default for fast builds)
        let target_64 = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert!(matches!(BackendKind::for_target(&target_64), BackendKind::Cranelift));
    }

    /// Test LLVM module creation
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_module_creation() {
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // Verify module can be created
        assert!(backend.create_module("test_module").is_ok());
    }

    /// Test LLVM function signature generation
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_function_signature() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // Test simple function signature: fn(i32, i32) -> i32
        let params = vec![T::I32, T::I32];
        let ret_type = T::I32;
        
        let sig = backend.create_function_signature("add", &params, &ret_type);
        assert!(sig.is_ok());
    }

    /// Test LLVM target triple mapping
    #[test]
    #[cfg(feature = "llvm")]
    fn test_target_triple_mapping() {
        // Test 32-bit x86
        let target_32 = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend_32 = LlvmBackend::new(target_32).unwrap();
        let triple_32 = backend_32.get_target_triple();
        assert!(triple_32.contains("i686") || triple_32.contains("i386"));
        
        // Test 64-bit x86
        let target_64 = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend_64 = LlvmBackend::new(target_64).unwrap();
        let triple_64 = backend_64.get_target_triple();
        assert!(triple_64.contains("x86_64"));
        
        // Test 32-bit ARM
        let target_arm = Target::new(TargetArch::Arm, TargetOS::Linux);
        let backend_arm = LlvmBackend::new(target_arm).unwrap();
        let triple_arm = backend_arm.get_target_triple();
        assert!(triple_arm.contains("arm") || triple_arm.contains("armv7"));
        
        // Test 32-bit RISC-V
        let target_rv32 = Target::new(TargetArch::Riscv32, TargetOS::Linux);
        let backend_rv32 = LlvmBackend::new(target_rv32).unwrap();
        let triple_rv32 = backend_rv32.get_target_triple();
        assert!(triple_rv32.contains("riscv32"));
    }
    /// Test LLVM IR generation for simple function
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_ir_generation() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        // Create module
        backend.create_module("test_ir").unwrap();
        
        // Create function: fn add(i32, i32) -> i32
        backend.create_function_signature("add", &[T::I32, T::I32], &T::I32).unwrap();
        
        // Get IR
        let ir = backend.get_ir().unwrap();
        
        // Verify IR contains our function
        assert!(ir.contains("define"));
        assert!(ir.contains("add"));
        assert!(ir.contains("i32"));
        
        // Verify module
        backend.verify().unwrap();
    }

    /// Test LLVM IR for different types
    #[test]
    #[cfg(feature = "llvm")]
    fn test_llvm_ir_different_types() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::X86, TargetOS::Linux);  // 32-bit!
        let backend = LlvmBackend::new(target).unwrap();
        
        backend.create_module("types_test").unwrap();
        
        // Test i64 function
        backend.create_function_signature("fn_i64", &[T::I64], &T::I64).unwrap();
        
        // Test f32 function
        backend.create_function_signature("fn_f32", &[T::F32, T::F32], &T::F32).unwrap();
        
        // Test f64 function
        backend.create_function_signature("fn_f64", &[T::F64], &T::F64).unwrap();
        
        let ir = backend.get_ir().unwrap();
        
        // Check that functions were created
        assert!(ir.contains("fn_i64"));
        assert!(ir.contains("fn_f32"));
        assert!(ir.contains("fn_f64"));
        assert!(ir.contains("i64"));
        assert!(ir.contains("float"));
        assert!(ir.contains("double"));
        
        backend.verify().unwrap();
    }

    /// Test 32-bit target has correct triple in IR
    #[test]
    #[cfg(feature = "llvm")]
    fn test_32bit_target_triple_in_ir() {
        let target = Target::new(TargetArch::Arm, TargetOS::Linux);  // ARMv7 32-bit
        let backend = LlvmBackend::new(target).unwrap();
        
        backend.create_module("armv7_test").unwrap();
        
        let ir = backend.get_ir().unwrap();
        
        // Verify target triple is in IR
        assert!(ir.contains("target triple"));
        assert!(ir.contains("armv7") || ir.contains("arm"));
    }
}

    /// Test complete function compilation with basic blocks
    #[test]
    #[cfg(feature = "llvm")]
    fn test_complete_function_compilation() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        backend.create_module("complete_fn").unwrap();
        
        // Compile function: fn answer() -> i32 { return 42; }
        backend.compile_simple_function("answer", &[], &T::I32, 42).unwrap();
        
        let ir = backend.get_ir().unwrap();
        
        // Verify function exists
        assert!(ir.contains("define"));
        assert!(ir.contains("answer"));
        
        // Verify basic block
        assert!(ir.contains("entry:"));
        
        // Verify return instruction with constant
        assert!(ir.contains("ret i32 42"));
        
        backend.verify().unwrap();
    }

    /// Test 32-bit function compilation
    #[test]
    #[cfg(feature = "llvm")]
    fn test_32bit_function_compilation() {
        use crate::hir::TypeId as T;
        
        // Use actual 32-bit target (i686)
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let backend = LlvmBackend::new(target).unwrap();
        
        backend.create_module("i686_test").unwrap();
        
        // Compile function for 32-bit target
        backend.compile_simple_function("get_value", &[], &T::I32, 100).unwrap();
        
        let ir = backend.get_ir().unwrap();
        
        // Verify it's targeting i686
        assert!(ir.contains("i686"));
        assert!(ir.contains("get_value"));
        assert!(ir.contains("ret i32 100"));
        
        backend.verify().unwrap();
    }

    /// Test function with parameters
    #[test]
    #[cfg(feature = "llvm")]
    fn test_function_with_parameters() {
        use crate::hir::TypeId as T;
        
        let target = Target::new(TargetArch::Arm, TargetOS::Linux);  // ARMv7
        let backend = LlvmBackend::new(target).unwrap();
        
        backend.create_module("params_test").unwrap();
        
        // Function with 2 i32 parameters (though we ignore them for now)
        backend.compile_simple_function("dummy", &[T::I32, T::I32], &T::I32, 0).unwrap();
        
        let ir = backend.get_ir().unwrap();
        
        // Verify parameters in signature
        assert!(ir.contains("i32"));
        assert!(ir.contains("dummy"));
        assert!(ir.contains("armv7") || ir.contains("arm"));
        
        backend.verify().unwrap();
    }
