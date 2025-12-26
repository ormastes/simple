//! Control flow tests - if/else, phi nodes, conditional branches.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test control flow - if/else with phi
#[test]
#[cfg(feature = "llvm")]
fn test_control_flow_conditional() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("control_flow").unwrap();

    // fn check(x: i32) -> i32 { if (x > 0) { return 1; } else { return 0; } }
    backend
        .compile_conditional_function("check", &T::I32, &T::I32, 1, 0)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify control flow elements
    assert!(ir.contains("entry:"));
    assert!(ir.contains("then:"));
    assert!(ir.contains("else:"));
    assert!(ir.contains("merge:"));
    assert!(ir.contains("phi"));
    assert!(ir.contains("br i1")); // conditional branch
    assert!(ir.contains("icmp")); // integer compare

    backend.verify().unwrap();
}

/// Test control flow on 32-bit target (i686)
#[test]
#[cfg(feature = "llvm")]
fn test_control_flow_32bit() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86, TargetOS::Linux); // i686
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("i686_control").unwrap();

    // Conditional on 32-bit target
    backend
        .compile_conditional_function("test32", &T::I32, &T::I32, 42, 0)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify 32-bit target
    assert!(ir.contains("i686"));

    // Verify control flow works
    assert!(ir.contains("phi"));
    assert!(ir.contains("br i1"));

    backend.verify().unwrap();
}

/// Test control flow on ARMv7
#[test]
#[cfg(feature = "llvm")]
fn test_control_flow_armv7() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::Arm, TargetOS::Linux); // ARMv7
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("armv7_control").unwrap();

    backend
        .compile_conditional_function("arm_check", &T::I32, &T::I32, 7, 3)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify ARM target
    assert!(ir.contains("armv7") || ir.contains("arm"));

    // Verify control flow
    assert!(ir.contains("phi"));
    assert!(ir.contains("icmp"));

    backend.verify().unwrap();
}
