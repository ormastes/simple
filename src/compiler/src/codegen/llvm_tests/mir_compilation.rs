//! MIR compilation tests - testing MIR to LLVM translation.

use crate::codegen::llvm::*;
use simple_common::target::{Target, TargetArch, TargetOS};

fn test_mir_function_compilation() {
    use crate::hir::TypeId as T;
    use crate::mir::{BlockId, MirBlock, MirFunction, MirInst, MirModule, Terminator, VReg};
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
    func.blocks[0].terminator = Terminator::Return(Some(v0));

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
    use crate::mir::MirModule;
    use crate::mir::{MirFunction, MirLocal};
    use crate::mir::{MirInst, Terminator, VReg};
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
        is_ghost: false,
    });
    func.params.push(MirLocal {
        name: "b".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
        is_ghost: false,
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
    func.blocks[0].terminator = Terminator::Return(Some(v2));

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
    use crate::mir::{BlockId, MirInst, Terminator, VReg};
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
        is_ghost: false,
    });

    let v0 = VReg(0); // parameter
    let v_true = VReg(1);
    let v_false = VReg(2);

    // Block 0: check condition
    func.blocks[0].instructions.push(MirInst::ConstBool {
        dest: v0,
        value: true,
    });
    func.blocks[0].terminator = Terminator::Branch {
        cond: v0,
        then_block: BlockId(1),
        else_block: BlockId(2),
    };

    // Block 1: then branch
    let mut then_block = MirBlock::new(BlockId(1));
    then_block.instructions.push(MirInst::ConstInt {
        dest: v_true,
        value: 1,
    });
    then_block.terminator = Terminator::Return(Some(v_true));
    func.blocks.push(then_block);

    // Block 2: else branch
    let mut else_block = MirBlock::new(BlockId(2));
    else_block.instructions.push(MirInst::ConstInt {
        dest: v_false,
        value: 0,
    });
    else_block.terminator = Terminator::Return(Some(v_false));
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
    use super::helpers::create_test_backend;
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let backend = create_test_backend("float_test");

    // fn test() -> f64 { return 3.15; }
    let mut func = MirFunction::new("test".to_string(), T::F64, Visibility::Public);

    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstFloat {
        dest: v0,
        value: 3.15,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v0));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("3.15"));
    assert!(ir.contains("ret double"));

    backend.verify().unwrap();
}

/// Test MIR unary operation compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_unaryop() {
    use super::helpers::create_test_backend_with_arch;
    use crate::hir::{TypeId as T, UnaryOp};
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_common::target::TargetArch;
    use simple_parser::ast::Visibility;

    let backend = create_test_backend_with_arch("unary_test", TargetArch::Aarch64);

    // fn neg(x: i32) -> i32 { return -x; }
    let mut func = MirFunction::new("neg".to_string(), T::I32, Visibility::Public);

    use crate::mir::effects::LocalKind;
    use crate::mir::MirLocal;
    func.params.push(MirLocal {
        name: "x".to_string(),
        ty: T::I32,
        kind: LocalKind::Parameter,
        is_ghost: false,
    });

    let v0 = VReg(0); // parameter
    let v1 = VReg(1); // result

    func.blocks[0].instructions.push(MirInst::UnaryOp {
        dest: v1,
        op: UnaryOp::Neg,
        operand: v0,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v1));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("sub")); // Negation is sub 0, x

    backend.verify().unwrap();
}

/// Test MIR memory operations (Load/Store)
#[test]
#[cfg(feature = "llvm")]
fn test_mir_memory_ops() {
    use super::helpers::create_test_backend_with_arch;
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_common::target::TargetArch;
    use simple_parser::ast::Visibility;

    let backend = create_test_backend_with_arch("mem_test", TargetArch::RiscV64);

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
    func.blocks[0].terminator = Terminator::Return(Some(v2));

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
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
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
    func.blocks[0].terminator = Terminator::Return(Some(v0));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("hello"));
    assert!(ir.contains("@str"));

    backend.verify().unwrap();
}

/// Test MIR struct initialization and field access
#[test]
#[cfg(feature = "llvm")]
fn test_mir_struct_ops() {
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("struct_test").unwrap();

    // fn test() -> i64 { let s = {x: 10, y: 20}; return s.x; }
    let mut func = MirFunction::new("test".to_string(), T::I64, Visibility::Public);

    let v0 = VReg(0); // const 10
    let v1 = VReg(1); // const 20
    let v2 = VReg(2); // struct
    let v3 = VReg(3); // field value

    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 10,
    });
    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v1,
        value: 20,
    });
    func.blocks[0].instructions.push(MirInst::StructInit {
        dest: v2,
        fields: vec![("x".to_string(), v0), ("y".to_string(), v1)],
        ty: T::I64,
    });
    func.blocks[0].instructions.push(MirInst::FieldGet {
        dest: v3,
        object: v2,
        field_index: 0,
        ty: T::I64,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v3));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("struct"));
    assert!(ir.contains("getelementptr"));
    assert!(ir.contains("load"));

    backend.verify().unwrap();
}

/// Test MIR array and tuple operations
#[test]
#[cfg(feature = "llvm")]
fn test_mir_array_tuple() {
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("array_test").unwrap();

    // fn test() -> i64 { let arr = [1, 2, 3]; return arr[1]; }
    let mut func = MirFunction::new("test".to_string(), T::I64, Visibility::Public);

    let v0 = VReg(0); // const 1
    let v1 = VReg(1); // const 2
    let v2 = VReg(2); // const 3
    let v3 = VReg(3); // array
    let v4 = VReg(4); // index
    let v5 = VReg(5); // result

    func.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v0, value: 1 });
    func.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v1, value: 2 });
    func.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v2, value: 3 });
    func.blocks[0].instructions.push(MirInst::ArrayLit {
        dest: v3,
        elements: vec![v0, v1, v2],
    });
    func.blocks[0]
        .instructions
        .push(MirInst::ConstInt { dest: v4, value: 1 });
    func.blocks[0].instructions.push(MirInst::IndexGet {
        dest: v5,
        collection: v3,
        index: v4,
    });
    func.blocks[0].terminator = Terminator::Return(Some(v5));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("array"));
    assert!(ir.contains("getelementptr"));

    backend.verify().unwrap();
}

/// Test MIR symbol constant compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_symbol_const() {
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("sym_test").unwrap();

    // fn test() -> *i8 { return :my_symbol; }
    let mut func = MirFunction::new("test".to_string(), T::Pointer, Visibility::Public);

    let v0 = VReg(0);
    func.blocks[0].instructions.push(MirInst::ConstSymbol {
        dest: v0,
        name: "my_symbol".to_string(),
    });
    func.blocks[0].terminator = Terminator::Return(Some(v0));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("my_symbol"));
    assert!(ir.contains("@sym_"));

    backend.verify().unwrap();
}

/// Test MIR function call compilation
#[test]
#[cfg(feature = "llvm")]
fn test_mir_function_call() {
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{CallTarget, MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("call_test").unwrap();

    // fn test() -> i64 { return add(10, 20); }
    let mut func = MirFunction::new("test".to_string(), T::I64, Visibility::Public);

    let v0 = VReg(0); // const 10
    let v1 = VReg(1); // const 20
    let v2 = VReg(2); // result

    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 10,
    });
    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v1,
        value: 20,
    });
    func.blocks[0].instructions.push(MirInst::Call {
        dest: Some(v2),
        target: CallTarget::Pure("add".to_string()),
        args: vec![v0, v1],
    });
    func.blocks[0].terminator = Terminator::Return(Some(v2));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("call"));
    assert!(ir.contains("add"));

    backend.verify().unwrap();
}

/// Test MIR InterpCall compilation (interpreter fallback)
#[test]
#[cfg(feature = "llvm")]
fn test_mir_interp_call() {
    use crate::hir::TypeId as T;
    use crate::mir::MirFunction;
    use crate::mir::{MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
    let backend = LlvmBackend::new(target).unwrap();

    backend.create_module("interp_test").unwrap();

    // fn test() -> i64 { return interp_call("complex_fn", 42); }
    let mut func = MirFunction::new("test".to_string(), T::I64, Visibility::Public);

    let v0 = VReg(0); // const 42
    let v1 = VReg(1); // result

    func.blocks[0].instructions.push(MirInst::ConstInt {
        dest: v0,
        value: 42,
    });
    func.blocks[0].instructions.push(MirInst::InterpCall {
        dest: Some(v1),
        func_name: "complex_fn".to_string(),
        args: vec![v0],
    });
    func.blocks[0].terminator = Terminator::Return(Some(v1));

    backend.compile_function(&func).unwrap();

    let ir = backend.get_ir().unwrap();
    assert!(ir.contains("rt_interp_call"));
    assert!(ir.contains("complex_fn"));

    backend.verify().unwrap();
}
