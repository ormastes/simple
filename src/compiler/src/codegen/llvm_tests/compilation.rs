//! Compilation and backend tests - basic compilation and backend trait tests.

use crate::codegen::backend_trait::NativeBackend;
use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

/// Test simple function compilation with real MIR
#[test]
#[cfg(feature = "llvm")]
fn test_compile_simple_function() {
    use crate::hir::TypeId as T;
    use crate::mir::{MirFunction, MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("simple_fn").unwrap();

    // Create a simple function: fn answer() -> i64 { return 42; }
    let mut func = MirFunction::new("answer".to_string(), T::I64, Visibility::Public);
    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 42,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v0));

    backend.compile_function(&func).unwrap();
    backend.verify().unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("answer"));
    assert!(ir.contains("ret i64 42"));
    assert_eq!(backend.name(), "llvm");
}

/// Test that backend can emit object code with real MIR module
#[test]
#[cfg(feature = "llvm")]
fn test_emit_object_code() {
    use crate::hir::TypeId as T;
    use crate::mir::{MirFunction, MirInst, MirModule, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let mut backend = LlvmBackend::new(target).unwrap();

    // Create a MIR module with a simple function
    let mut mir_module = MirModule::new();
    mir_module.name = Some("obj_test".to_string());

    let mut func = MirFunction::new("main".to_string(), T::I64, Visibility::Public);
    let v0 = VReg(0);
    func.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v0, value: 0 });
    func.blocks[0].terminator = Terminator::Return(Some(v0));
    mir_module.functions.push(func);

    // Compile through the NativeBackend trait
    let obj_code = backend.compile(&mir_module).unwrap();
    assert!(!obj_code.is_empty());
    assert!(LlvmBackend::supports_target(&target));
}

/// Test backend without llvm feature just checks target support
#[test]
#[cfg(not(feature = "llvm"))]
fn test_emit_object_code() {
    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
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

/// Test that backend can handle multiple functions
#[test]
#[cfg(feature = "llvm")]
fn test_compile_multiple_functions() {
    use crate::hir::TypeId as T;
    use crate::mir::effects::LocalKind;
    use crate::mir::{MirFunction, MirInst, MirLocal, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("multi_fn").unwrap();

    // First function: fn one() -> i64 { return 1; }
    let mut func1 = MirFunction::new("one".to_string(), T::I64, Visibility::Public);
    let v0 = VReg(0);
    func1.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v0, value: 1 });
    func1.blocks[0].terminator = Terminator::Return(Some(v0));
    backend.compile_function(&func1).unwrap();

    // Second function: fn double(x: i64) -> i64 { return x + x; }
    let mut func2 = MirFunction::new("double".to_string(), T::I64, Visibility::Public);
    func2.params.push(MirLocal {
        name: "x".to_string(),
        ty: T::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });
    let v0 = VReg(0); // parameter
    let v1 = VReg(1); // result
    func2.blocks[0].instructions.push(MirInst::BinOp {
        dest: v1,
        op: crate::hir::BinOp::Add,
        left: v0,
        right: v0,
    });
    func2.blocks[0].terminator = Terminator::Return(Some(v1));
    backend.compile_function(&func2).unwrap();

    backend.verify().unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("one"));
    assert!(ir.contains("double"));
    assert_eq!(backend.pointer_width(), 64);
}

/// Test NativeBackend trait implementation
#[test]
#[cfg(feature = "llvm")]
fn test_native_backend_trait() {
    use crate::hir::TypeId as T;
    use crate::mir::{MirFunction, MirInst, MirModule, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let mut backend = LlvmBackend::new(target).unwrap();

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

    // Test compile through NativeBackend trait
    let mut mir_module = MirModule::new();
    mir_module.name = Some("trait_test".to_string());

    let mut func = MirFunction::new("test".to_string(), T::I64, Visibility::Public);
    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 123,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v0));
    mir_module.functions.push(func);

    // Compile through trait - should produce object code
    let obj_code = backend.compile(&mir_module).unwrap();
    assert!(!obj_code.is_empty());
}

/// Test backend selection logic (doesn't require llvm feature)
#[test]
fn test_backend_kind_selection() {
    use crate::codegen::BackendKind;

    // 32-bit targets should select LLVM when llvm feature is available
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

    // ARM 32-bit targets should prefer LLVM when available
    let target_arm = Target::new(TargetArch::Arm, TargetOS::Linux);
    let kind_arm = BackendKind::for_target(&target_arm);
    #[cfg(feature = "llvm")]
    assert_eq!(kind_arm, BackendKind::Llvm);
    #[cfg(not(feature = "llvm"))]
    assert_eq!(kind_arm, BackendKind::Cranelift);
}
