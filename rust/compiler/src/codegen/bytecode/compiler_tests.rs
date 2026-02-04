//! Tests for the MIR-to-bytecode compiler.

use simple_parser::ast::Visibility;
use simple_runtime::bytecode::vm::BytecodeVM;
use simple_runtime::RuntimeValue;

use super::compiler::BytecodeCompiler;
use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{BlockId, LocalKind, MirBlock, MirFunction, MirInst, MirLocal, Terminator, VReg};

/// Helper to create a simple MIR function with one block.
fn make_function(name: &str, params: Vec<MirLocal>, instructions: Vec<MirInst>, terminator: Terminator) -> MirFunction {
    let mut func = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
    func.params = params;
    func.blocks[0].instructions = instructions;
    func.blocks[0].terminator = terminator;
    func
}

/// Helper to create a param local.
fn param(name: &str) -> MirLocal {
    MirLocal {
        name: name.to_string(),
        ty: TypeId::I64,
        kind: LocalKind::Parameter,
        is_ghost: false,
    }
}

#[test]
fn test_compile_const_int_return() {
    // fn foo() -> i64 { 42 }
    let func = make_function(
        "foo",
        vec![],
        vec![MirInst::ConstInt {
            dest: VReg(0),
            value: 42,
        }],
        Terminator::Return(Some(VReg(0))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    assert_eq!(compiled.metadata.name, "foo");
    assert_eq!(compiled.metadata.param_count, 0);

    // Execute
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_compile_add_two_params() {
    // fn add(a: i64, b: i64) -> i64 { a + b }
    let func = make_function(
        "add",
        vec![param("a"), param("b")],
        vec![MirInst::BinOp {
            dest: VReg(2),
            op: BinOp::Add,
            left: VReg(0),
            right: VReg(1),
        }],
        Terminator::Return(Some(VReg(2))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    assert_eq!(compiled.metadata.param_count, 2);

    // Execute via call_function
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata]);

    let args = [RuntimeValue::from_int(15), RuntimeValue::from_int(27)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_compile_arithmetic_expression() {
    // fn expr() -> i64 { (3 + 4) * 2 }
    let func = make_function(
        "expr",
        vec![],
        vec![
            MirInst::ConstInt {
                dest: VReg(0),
                value: 3,
            },
            MirInst::ConstInt {
                dest: VReg(1),
                value: 4,
            },
            MirInst::BinOp {
                dest: VReg(2),
                op: BinOp::Add,
                left: VReg(0),
                right: VReg(1),
            },
            MirInst::ConstInt {
                dest: VReg(3),
                value: 2,
            },
            MirInst::BinOp {
                dest: VReg(4),
                op: BinOp::Mul,
                left: VReg(2),
                right: VReg(3),
            },
        ],
        Terminator::Return(Some(VReg(4))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_int(), 14); // (3 + 4) * 2 = 14
}

#[test]
fn test_compile_comparison() {
    // fn is_less(a: i64, b: i64) -> bool { a < b }
    let func = make_function(
        "is_less",
        vec![param("a"), param("b")],
        vec![MirInst::BinOp {
            dest: VReg(2),
            op: BinOp::Lt,
            left: VReg(0),
            right: VReg(1),
        }],
        Terminator::Return(Some(VReg(2))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata]);

    let args = [RuntimeValue::from_int(3), RuntimeValue::from_int(5)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_bool(), true);
}

#[test]
fn test_compile_branch() {
    // fn max(a: i64, b: i64) -> i64 {
    //     if a > b: a
    //     else: b
    // }
    let mut func = MirFunction::new("max".to_string(), TypeId::I64, Visibility::Public);
    func.params = vec![param("a"), param("b")];

    // Block 0 (entry): compare and branch
    func.blocks[0].instructions = vec![MirInst::BinOp {
        dest: VReg(2),
        op: BinOp::Gt,
        left: VReg(0),
        right: VReg(1),
    }];
    func.blocks[0].terminator = Terminator::Branch {
        cond: VReg(2),
        then_block: BlockId(1),
        else_block: BlockId(2),
    };

    // Block 1 (then): return a
    func.blocks.push(MirBlock {
        id: BlockId(1),
        instructions: vec![],
        terminator: Terminator::Return(Some(VReg(0))),
    });

    // Block 2 (else): return b
    func.blocks.push(MirBlock {
        id: BlockId(2),
        instructions: vec![],
        terminator: Terminator::Return(Some(VReg(1))),
    });

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    // Test: max(10, 5) = 10
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata.clone()]);

    let args = [RuntimeValue::from_int(10), RuntimeValue::from_int(5)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 10);

    // Test: max(3, 7) = 7
    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata]);

    let args = [RuntimeValue::from_int(3), RuntimeValue::from_int(7)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 7);
}

#[test]
fn test_compile_void_return() {
    // fn noop() {}
    let func = make_function("noop", vec![], vec![], Terminator::Return(None));

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    let result = vm.execute().expect("Execution failed");
    assert!(result.is_nil());
}

#[test]
fn test_compile_copy() {
    // fn identity(x: i64) -> i64 { x }
    let func = make_function(
        "identity",
        vec![param("x")],
        vec![MirInst::Copy {
            dest: VReg(1),
            src: VReg(0),
        }],
        Terminator::Return(Some(VReg(1))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata]);

    let args = [RuntimeValue::from_int(99)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), 99);
}

#[test]
fn test_compile_negation() {
    // fn negate(x: i64) -> i64 { -x }
    let func = make_function(
        "negate",
        vec![param("x")],
        vec![MirInst::UnaryOp {
            dest: VReg(1),
            op: UnaryOp::Neg,
            operand: VReg(0),
        }],
        Terminator::Return(Some(VReg(1))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    vm.set_functions(vec![compiled.metadata]);

    let args = [RuntimeValue::from_int(42)];
    let result = vm.call_function(0, &args).expect("Execution failed");
    assert_eq!(result.as_int(), -42);
}

#[test]
fn test_compile_bool_const() {
    // fn get_true() -> bool { true }
    let func = make_function(
        "get_true",
        vec![],
        vec![MirInst::ConstBool {
            dest: VReg(0),
            value: true,
        }],
        Terminator::Return(Some(VReg(0))),
    );

    let mut compiler = BytecodeCompiler::new();
    let compiled = compiler.compile_function(&func).expect("Compilation failed");

    let mut vm = BytecodeVM::new();
    vm.load_bytecode(&compiled.code);
    let result = vm.execute().expect("Execution failed");
    assert_eq!(result.as_bool(), true);
}
