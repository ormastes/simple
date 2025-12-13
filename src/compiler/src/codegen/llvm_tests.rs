/// LLVM backend tests
///
/// Tests for LLVM-based code generation supporting 32-bit and 64-bit targets.
/// This backend complements Cranelift by providing broader architecture support.

#[cfg(test)]
mod tests {
    use crate::codegen::llvm::*;
    use simple_common::target::{Arch, Os, Target};

    /// Test that LLVM backend can be created for 64-bit x86_64
    #[test]
    fn test_llvm_backend_create_x86_64() {
        let target = Target {
            arch: Arch::X86_64,
            os: Os::Linux,
            pointer_width: 64,
        };
        
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit i686
    #[test]
    fn test_llvm_backend_create_i686() {
        let target = Target {
            arch: Arch::X86,
            os: Os::Linux,
            pointer_width: 32,
        };
        
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit ARMv7
    #[test]
    fn test_llvm_backend_create_armv7() {
        let target = Target {
            arch: Arch::ArmV7,
            os: Os::Linux,
            pointer_width: 32,
        };
        
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test that LLVM backend can be created for 32-bit RISC-V
    #[test]
    fn test_llvm_backend_create_riscv32() {
        let target = Target {
            arch: Arch::RiscV32,
            os: Os::Linux,
            pointer_width: 32,
        };
        
        let backend = LlvmBackend::new(target);
        assert!(backend.is_ok());
    }

    /// Test LLVM type mapping for basic types
    #[test]
    fn test_llvm_type_mapping() {
        let target = Target {
            arch: Arch::X86_64,
            os: Os::Linux,
            pointer_width: 64,
        };
        
        let backend = LlvmBackend::new(target).unwrap();
        
        // Test integer types
        assert!(backend.map_type(&Type::I32).is_ok());
        assert!(backend.map_type(&Type::I64).is_ok());
        assert!(backend.map_type(&Type::U32).is_ok());
        assert!(backend.map_type(&Type::U64).is_ok());
        
        // Test floating point types
        assert!(backend.map_type(&Type::F32).is_ok());
        assert!(backend.map_type(&Type::F64).is_ok());
        
        // Test bool
        assert!(backend.map_type(&Type::Bool).is_ok());
    }

    /// Test pointer width consistency
    #[test]
    fn test_pointer_width_32bit() {
        let target = Target {
            arch: Arch::X86,
            os: Os::Linux,
            pointer_width: 32,
        };
        
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 32);
    }

    /// Test pointer width consistency for 64-bit
    #[test]
    fn test_pointer_width_64bit() {
        let target = Target {
            arch: Arch::X86_64,
            os: Os::Linux,
            pointer_width: 64,
        };
        
        let backend = LlvmBackend::new(target).unwrap();
        assert_eq!(backend.pointer_width(), 64);
    }

    /// Test simple function compilation
    #[test]
    fn test_compile_simple_function() {
        let target = Target {
            arch: Arch::X86_64,
            os: Os::Linux,
            pointer_width: 64,
        };
        
        let backend = LlvmBackend::new(target).unwrap();
        
        // Create a simple function: fn add(a: i32, b: i32) -> i32 { a + b }
        let func = MirFunction {
            name: "add".to_string(),
            params: vec![
                (VReg(0), Type::I32),
                (VReg(1), Type::I32),
            ],
            return_type: Type::I32,
            blocks: vec![
                MirBlock {
                    id: BlockId(0),
                    instructions: vec![
                        MirInstr::BinOp {
                            dst: VReg(2),
                            op: BinOpKind::Add,
                            lhs: VReg(0),
                            rhs: VReg(1),
                        },
                        MirInstr::Return(Some(VReg(2))),
                    ],
                },
            ],
        };
        
        let result = backend.compile_function(&func);
        assert!(result.is_ok());
    }

    /// Test that backend can emit object code
    #[test]
    fn test_emit_object_code() {
        let target = Target {
            arch: Arch::X86_64,
            os: Os::Linux,
            pointer_width: 64,
        };
        
        let backend = LlvmBackend::new(target).unwrap();
        
        // Compile a simple module
        let module = MirModule {
            functions: vec![],
        };
        
        let object_bytes = backend.emit_object(&module);
        assert!(object_bytes.is_ok());
        // Empty module should still produce valid (albeit minimal) object
    }
}
