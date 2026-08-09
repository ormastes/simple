//! Type mapping tests - LLVM type system and pointer width tests.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

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
