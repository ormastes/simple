//! IR generation tests - LLVM module, function signatures, and IR generation.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test LLVM module creation
#[test]
#[cfg(feature = "llvm")]
fn test_llvm_module_creation() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    let result = backend.create_module("test_module");
    assert!(result.is_ok());
}

/// Test function signature creation
#[test]
#[cfg(feature = "llvm")]
fn test_llvm_function_signature() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("test_mod").unwrap();

    // Create function: fn add(i32, i32) -> i32
    let result = backend.create_function_signature("add", &[T::I32, T::I32], &T::I32);
    assert!(result.is_ok());
}

/// Test target triple mapping for different architectures
#[test]
#[cfg(feature = "llvm")]
fn test_target_triple_mapping() {
    // Test 64-bit x86_64
    let target_x64 = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend_x64 = LlvmBackend::new(target_x64).unwrap();
    let triple_x64 = backend_x64.get_target_triple();
    assert!(triple_x64.contains("x86_64"));

    // Test 32-bit i686
    let target_x86 = Target::new(TargetArch::X86, TargetOS::Linux);
    let backend_x86 = LlvmBackend::new(target_x86).unwrap();
    let triple_x86 = backend_x86.get_target_triple();
    assert!(triple_x86.contains("i686") || triple_x86.contains("i386"));

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
    backend
        .create_function_signature("add", &[T::I32, T::I32], &T::I32)
        .unwrap();

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

    let target = Target::new(TargetArch::X86, TargetOS::Linux); // 32-bit!
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("types_test").unwrap();

    // Test i64 function
    backend.create_function_signature("fn_i64", &[T::I64], &T::I64).unwrap();

    // Test f32 function
    backend
        .create_function_signature("fn_f32", &[T::F32, T::F32], &T::F32)
        .unwrap();

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
    let target = Target::new(TargetArch::Arm, TargetOS::Linux); // ARMv7 32-bit
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("armv7_test").unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify target triple is in IR
    assert!(ir.contains("target triple"));
    assert!(ir.contains("armv7") || ir.contains("arm"));
}
