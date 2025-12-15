//! Compilation and backend tests - basic compilation and backend trait tests.

use crate::codegen::backend_trait::NativeBackend;
use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

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
    assert!(LlvmBackend::supports_target(&Target::new(
        TargetArch::X86,
        TargetOS::Linux
    )));
    assert!(LlvmBackend::supports_target(&Target::new(
        TargetArch::X86_64,
        TargetOS::Linux
    )));
    assert!(LlvmBackend::supports_target(&Target::new(
        TargetArch::Arm,
        TargetOS::Linux
    )));
    assert!(LlvmBackend::supports_target(&Target::new(
        TargetArch::Riscv32,
        TargetOS::Linux
    )));

    // TODO: Test compile through trait when we have proper MIR construction
}

/// Test backend selection logic (doesn't require llvm feature)
#[test]
fn test_backend_kind_selection() {
    use crate::codegen::BackendKind;

    // 32-bit targets should select LLVM
    let target_32 = Target::new(TargetArch::X86, TargetOS::Linux);
    let kind_32 = BackendKind::for_target(&target_32);
    #[cfg(feature = "llvm")]
    assert_eq!(kind_32, BackendKind::Llvm);
    #[cfg(not(feature = "llvm"))]
    assert_eq!(kind_32, BackendKind::Cranelift);

    // 64-bit targets prefer Cranelift but can use LLVM
    let target_64 = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let kind_64 = BackendKind::for_target(&target_64);
    // Always prefer Cranelift for 64-bit when available
    assert_eq!(kind_64, BackendKind::Cranelift);

    // ARM targets should prefer LLVM for better support
    let target_arm = Target::new(TargetArch::Arm, TargetOS::Linux);
    let kind_arm = BackendKind::for_target(&target_arm);
    #[cfg(feature = "llvm")]
    assert_eq!(kind_arm, BackendKind::Llvm);
    #[cfg(not(feature = "llvm"))]
    assert_eq!(kind_arm, BackendKind::Cranelift);
}
