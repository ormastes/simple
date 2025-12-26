//! Function compilation tests - complete functions with basic blocks and parameters.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test complete function compilation with basic blocks
#[test]
#[cfg(feature = "llvm")]
fn test_complete_function_compilation() {
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("complete_fn").unwrap();

    // Compile function: fn answer() -> i32 { return 42; }
    backend
        .compile_simple_function("answer", &[], &T::I32, 42)
        .unwrap();

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
    backend
        .compile_simple_function("get_value", &[], &T::I32, 100)
        .unwrap();

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

    let target = Target::new(TargetArch::Arm, TargetOS::Linux); // ARMv7
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("params_test").unwrap();

    // Function with 2 i32 parameters (though we ignore them for now)
    backend
        .compile_simple_function("dummy", &[T::I32, T::I32], &T::I32, 0)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify parameters in signature
    assert!(ir.contains("i32"));
    assert!(ir.contains("dummy"));
    assert!(ir.contains("armv7") || ir.contains("arm"));

    backend.verify().unwrap();
}
