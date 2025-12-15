//! Object emission tests - ELF object file generation for different targets.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test object file emission for x86_64
#[test]
#[cfg(feature = "llvm")]
fn test_object_emission_x86_64() {
    use crate::hir::TypeId as T;
    use crate::mir::MirModule;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("obj_test").unwrap();

    // Create a simple function
    backend
        .compile_simple_function("main", &[], &T::I32, 0)
        .unwrap();

    // Emit object code
    let mir_module = MirModule::default();
    let object_code = backend.emit_object(&mir_module).unwrap();

    // Verify we got some object code
    assert!(!object_code.is_empty());

    // ELF magic number for x86_64 Linux
    assert_eq!(&object_code[0..4], b"\x7fELF");
}

/// Test object code emission for 32-bit i686
#[test]
#[cfg(feature = "llvm")]
fn test_object_emission_i686() {
    use crate::hir::TypeId as T;
    use crate::mir::MirModule;

    let target = Target::new(TargetArch::X86, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("i686_obj").unwrap();

    // Create function with binary operation
    backend
        .compile_binop_function(
            "add",
            &T::I32,
            &T::I32,
            &T::I32,
            crate::codegen::llvm::BinOp::Add,
        )
        .unwrap();

    // Emit object code
    let mir_module = MirModule::default();
    let object_code = backend.emit_object(&mir_module).unwrap();

    // Verify object code generated
    assert!(!object_code.is_empty());
    assert_eq!(&object_code[0..4], b"\x7fELF");

    // Verify it's 32-bit ELF (class = 1)
    assert_eq!(object_code[4], 1); // ELFCLASS32
}

/// Test object code emission for ARMv7
#[test]
#[cfg(feature = "llvm")]
fn test_object_emission_armv7() {
    use crate::hir::TypeId as T;
    use crate::mir::MirModule;

    let target = Target::new(TargetArch::Arm, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("arm_obj").unwrap();

    // Create control flow function
    backend
        .compile_conditional_function("check", &T::I32, &T::I32, 1, 0)
        .unwrap();

    // Emit object code
    let mir_module = MirModule::default();
    let object_code = backend.emit_object(&mir_module).unwrap();

    // Verify object code
    assert!(!object_code.is_empty());
    assert_eq!(&object_code[0..4], b"\x7fELF");

    // Verify it's 32-bit
    assert_eq!(object_code[4], 1); // ELFCLASS32
}

/// Test object code emission for RISC-V 32
#[test]
#[cfg(feature = "llvm")]
fn test_object_emission_riscv32() {
    use crate::hir::TypeId as T;
    use crate::mir::MirModule;

    let target = Target::new(TargetArch::Riscv32, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("rv32_obj").unwrap();

    // Create function
    backend
        .compile_simple_function("test", &[], &T::I32, 42)
        .unwrap();

    // Emit object code
    let mir_module = MirModule::default();
    let object_code = backend.emit_object(&mir_module).unwrap();

    // Verify object code
    assert!(!object_code.is_empty());
    assert_eq!(&object_code[0..4], b"\x7fELF");
    assert_eq!(object_code[4], 1); // ELFCLASS32
}

/// Test that object code is valid relocatable object
#[test]
#[cfg(feature = "llvm")]
fn test_object_is_relocatable() {
    use crate::hir::TypeId as T;
    use crate::mir::MirModule;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("reloc_test").unwrap();
    backend
        .compile_simple_function("func", &[], &T::I32, 123)
        .unwrap();

    let mir_module = MirModule::default();
    let object_code = backend.emit_object(&mir_module).unwrap();

    assert!(!object_code.is_empty());

    // ELF type should be ET_REL (relocatable, value 1)
    assert_eq!(object_code[16], 1); // e_type LSB
}

/// Test MIR function compilation
#[test]
#[cfg(feature = "llvm")]
