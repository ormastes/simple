//! Binary operation tests - integer and floating point arithmetic.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test binary operation compilation - integer add
#[test]
#[cfg(feature = "llvm")]
fn test_binop_integer_add() {
    use crate::codegen::llvm::BinOp;
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("binop_test").unwrap();

    // fn add(a: i32, b: i32) -> i32 { return a + b; }
    backend
        .compile_binop_function("add", &T::I32, &T::I32, &T::I32, BinOp::Add)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify IR contains add instruction
    assert!(ir.contains("add"));
    assert!(ir.contains("i32"));
    assert!(ir.contains("ret"));

    backend.verify().unwrap();
}

/// Test binary operations on 32-bit target
#[test]
#[cfg(feature = "llvm")]
fn test_binop_32bit_target() {
    use crate::codegen::llvm::BinOp;
    use crate::hir::TypeId as T;

    // Use i686 (32-bit x86)
    let target = Target::new(TargetArch::X86, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("i686_binop").unwrap();

    // Test all 4 operations
    backend
        .compile_binop_function("add", &T::I32, &T::I32, &T::I32, BinOp::Add)
        .unwrap();
    backend
        .compile_binop_function("sub", &T::I32, &T::I32, &T::I32, BinOp::Sub)
        .unwrap();
    backend
        .compile_binop_function("mul", &T::I32, &T::I32, &T::I32, BinOp::Mul)
        .unwrap();
    backend
        .compile_binop_function("div", &T::I32, &T::I32, &T::I32, BinOp::Div)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify all operations present
    assert!(ir.contains("add"));
    assert!(ir.contains("sub"));
    assert!(ir.contains("mul"));
    assert!(ir.contains("sdiv")); // signed division

    // Verify 32-bit target
    assert!(ir.contains("i686"));

    backend.verify().unwrap();
}

/// Test floating point binary operations
#[test]
#[cfg(feature = "llvm")]
fn test_binop_float() {
    use crate::codegen::llvm::BinOp;
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::Arm, TargetOS::Linux); // ARMv7
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("float_binop").unwrap();

    // fn fadd(a: f32, b: f32) -> f32 { return a + b; }
    backend
        .compile_binop_function("fadd", &T::F32, &T::F32, &T::F32, BinOp::Add)
        .unwrap();
    backend
        .compile_binop_function("fsub", &T::F32, &T::F32, &T::F32, BinOp::Sub)
        .unwrap();
    backend
        .compile_binop_function("fmul", &T::F32, &T::F32, &T::F32, BinOp::Mul)
        .unwrap();
    backend
        .compile_binop_function("fdiv", &T::F32, &T::F32, &T::F32, BinOp::Div)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify float operations
    assert!(ir.contains("fadd"));
    assert!(ir.contains("fsub"));
    assert!(ir.contains("fmul"));
    assert!(ir.contains("fdiv"));
    assert!(ir.contains("float"));

    backend.verify().unwrap();
}

/// Test 64-bit integer operations
#[test]
#[cfg(feature = "llvm")]
fn test_binop_i64() {
    use crate::codegen::llvm::BinOp;
    use crate::hir::TypeId as T;

    let target = Target::new(TargetArch::Riscv32, TargetOS::Linux); // RISC-V 32-bit
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("i64_binop").unwrap();

    // 64-bit operations on 32-bit target (important test!)
    backend
        .compile_binop_function("add64", &T::I64, &T::I64, &T::I64, BinOp::Add)
        .unwrap();
    backend
        .compile_binop_function("mul64", &T::I64, &T::I64, &T::I64, BinOp::Mul)
        .unwrap();

    let ir = backend.get_ir().unwrap();

    // Verify i64 operations on 32-bit target
    assert!(ir.contains("i64"));
    assert!(ir.contains("add"));
    assert!(ir.contains("mul"));
    assert!(ir.contains("riscv32"));

    backend.verify().unwrap();
}
