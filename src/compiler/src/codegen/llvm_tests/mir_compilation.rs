//! MIR compilation tests - testing MIR to LLVM translation.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

fn test_mir_function_compilation() {
    use crate::hir::TypeId as T;
    use crate::mir::instructions::{BlockId, MirInst, MirTerminator, VReg};
    use crate::mir::MirModule;
    use crate::mir::{MirBlock, MirFunction};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("mir_test").unwrap();

    // Create a simple MIR function: fn test() -> i32 { return 42; }
    let mut func = MirFunction::new("test".to_string(), T::I32, Visibility::Public);

    // Add instruction: const i64 42 -> v0
    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 42,
    });

    // Add terminator: return v0
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v0) });

    // Compile function
    backend.compile_function(&func).unwrap();

    // Verify IR
    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("define"));
    assert!(ir.contains("test"));
    assert!(ir.contains("ret i64 42"));

    backend.verify().unwrap();
}

/// Test MIR binary operation compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_binop_compilation() {
    use crate::hir::{BinOp, TypeId as T};
    use crate::mir::effects::LocalKind;
    use crate::mir::instructions::{MirInst, MirTerminator, VReg};
    use crate::mir::MirModule;
    use crate::mir::{MirFunction, MirLocal};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86, TargetOS::Linux); // i686
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("mir_binop").unwrap();

    // Create MIR function: fn add(a: i32, b: i32) -> i32 { return a + b; }
    let mut func = MirFunction::new("add".to_string(), T::I32, Visibility::Public);

    // Add parameters
    func.params.push(MirLocal {
        name: "a".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
    });
    func.params.push(MirLocal {
        name: "b".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
    });

    // Parameters map to v0 and v1
    let v0 = VReg(0);
    let v1 = VReg(1);
    let v2 = VReg(2);

    // Add instruction: v2 = add v0, v1
    func.blocks[0].instructions.push(MirInst::BinOp {
        dest: v2,
        op: BinOp::Add,
        left: v0,
        right: v1,
    });

    // Add terminator: return v2
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v2) });

    // Compile function
    backend.compile_function(&func).unwrap();

    // Verify IR
    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("i686"));
    assert!(ir.contains("add"));
    assert!(ir.contains("ret"));

    backend.verify().unwrap();
}

/// Test MIR control flow compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_control_flow_compilation() {
    use crate::hir::{BinOp, TypeId as T};
    use crate::mir::effects::LocalKind;
    use crate::mir::instructions::{BlockId, MirInst, MirTerminator, VReg};
    use crate::mir::{MirBlock, MirFunction, MirLocal};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::Arm, TargetOS::Linux); // ARMv7
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("mir_cf").unwrap();

    // Create MIR function with branching
    let mut func = MirFunction::new("check".to_string(), T::I32, Visibility::Public);

    // Add parameter
    func.params.push(MirLocal {
        name: "x".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
    });

    let v0 = VReg(0); // parameter
    let v_true = VReg(1);
    let v_false = VReg(2);

    // Block 0: check condition
    func.blocks[0].instructions.push(MirInst::ConstBool {
        dest: v0,
        value: true,
    });
    func.blocks[0].terminator = Some(MirTerminator::Branch {
        cond: v0,
        then_block: BlockId(1),
        else_block: BlockId(2),
    });

    // Block 1: then branch
    let mut then_block = MirBlock::new(BlockId(1));
    then_block.instructions.push(MirInst::ConstInt {
        dest: v_true,
        value: 1,
    });
    then_block.terminator = Some(MirTerminator::Return {
        value: Some(v_true),
    });
    func.blocks.push(then_block);

    // Block 2: else branch
    let mut else_block = MirBlock::new(BlockId(2));
    else_block.instructions.push(MirInst::ConstInt {
        dest: v_false,
        value: 0,
    });
    else_block.terminator = Some(MirTerminator::Return {
        value: Some(v_false),
    });
    func.blocks.push(else_block);

    // Compile function
    backend.compile_function(&func).unwrap();

    // Verify IR
    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("br i1"));
    assert!(ir.contains("bb1"));
    assert!(ir.contains("bb2"));

    backend.verify().unwrap();
}

/// Test MIR float constant compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_float_const() {
    use crate::hir::TypeId as T;
    use crate::mir::instructions::{MirInst, MirTerminator, VReg};
    use crate::mir::MirFunction;
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("float_test").unwrap();

    // fn test() -> f64 { return 3.14; }
    let mut func = MirFunction::new("test".to_string(), T::F64, Visibility::Public);

    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstFloat {
        dest: v0,
        value: 3.14,
    });
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v0) });

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("3.14"));
    assert!(ir.contains("ret double"));

    backend.verify().unwrap();
}

/// Test MIR unary operation compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_unaryop() {
    use crate::hir::{TypeId as T, UnaryOp};
    use crate::mir::instructions::{MirInst, MirTerminator, VReg};
    use crate::mir::MirFunction;
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::Aarch64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("unary_test").unwrap();

    // fn neg(x: i32) -> i32 { return -x; }
    let mut func = MirFunction::new("neg".to_string(), T::I32, Visibility::Public);

    use crate::mir::effects::LocalKind;
    use crate::mir::MirLocal;
    func.params.push(MirLocal {
        name: "x".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
    });

    let v0 = VReg(0); // parameter
    let v1 = VReg(1); // result

    func.blocks[0].instructions.push(MirInst::UnaryOp {
        dest: v1,
        op: UnaryOp::Neg,
        operand: v0,
    });
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v1) });

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("sub")); // Negation is sub 0, x

    backend.verify().unwrap();
}

/// Test MIR memory operations (Load/Store)
#[test]
#[cfg(feature = "llvm")]
fn test_mir_memory_ops() {
    use crate::hir::TypeId as T;
    use crate::mir::instructions::{MirInst, MirTerminator, VReg};
    use crate::mir::MirFunction;
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::RiscV64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("mem_test").unwrap();

    // fn test() -> i32 { let x = 42; return x; }
    let mut func = MirFunction::new("test".to_string(), T::I32, Visibility::Public);

    let v0 = VReg(0); // const 42
    let v1 = VReg(1); // alloca
    let v2 = VReg(2); // loaded value

    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 42,
    });
    func.blocks[0].instructions.push(MirInst::GcAlloc {
        dest: v1,
        ty: T::I32,
    });
    func.blocks[0].instructions.push(MirInst::Store {
        addr: v1,
        value: v0,
        ty: T::I32,
    });
    func.blocks[0].instructions.push(MirInst::Load {
        dest: v2,
        addr: v1,
        ty: T::I32,
    });
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v2) });

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("alloca"));
    assert!(ir.contains("store"));
    assert!(ir.contains("load"));

    backend.verify().unwrap();
}

/// Test MIR string constant compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_string_const() {
    use crate::hir::TypeId as T;
    use crate::mir::instructions::{MirInst, MirTerminator, VReg};
    use crate::mir::MirFunction;
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86, TargetOS::Linux); // i686
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("str_test").unwrap();

    // fn test() -> *i8 { return "hello"; }
    let mut func = MirFunction::new("test".to_string(), T::Pointer, Visibility::Public);

    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstString {
        dest: v0,
        value: "hello".to_string(),
    });
    func.blocks[0].terminator = Some(MirTerminator::Return { value: Some(v0) });

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("hello"));
    assert!(ir.contains("@str"));

    backend.verify().unwrap();
}
