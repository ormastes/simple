//! Backend creation tests - testing LLVM backend initialization.

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
