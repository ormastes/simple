//! Basic MIR lowering tests

use super::common::*;
use crate::hir::{BinOp, HirType};
use crate::mir::{BlockId, MirInst, Terminator};

#[test]
fn test_lower_simple_return() {
    let mir = compile_to_mir("fn test() -> i64:\n    return 42\n").unwrap();

    assert_eq!(mir.functions.len(), 1);
    let func = &mir.functions[0];
    assert_eq!(func.name, "test");

    let entry = func.block(BlockId(0)).unwrap();
    assert!(!entry.instructions.is_empty());
    assert!(matches!(entry.terminator, Terminator::Return(Some(_))));
}

#[test]
fn test_lower_preserves_labeled_tuple_type_registry() {
    let mir = compile_to_mir("fn pair() -> (left: i64, right: bool):\n    return (left: 7, right: true)\n").unwrap();

    let func = &mir.functions[0];
    let return_type = func.return_type;
    let Some(HirType::LabeledTuple(fields)) = mir.type_registry.get(return_type) else {
        panic!("expected labeled tuple return type in MIR type registry");
    };

    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0], ("left".to_string(), crate::hir::TypeId::I64));
    assert_eq!(fields[1], ("right".to_string(), crate::hir::TypeId::BOOL));
}

#[test]
fn test_lower_binary_op() {
    let mir = compile_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have: load a, load b, add, return
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::BinOp { op: BinOp::Add, .. })));
}

#[test]
fn test_lower_bitfield_field_read_write() {
    let mir = compile_to_mir(
        r#"
bitfield Rv32Instruction(u32):
    opcode: 7
    rd: 5
    funct3: 3
    rs1: 5
    rs2: 5
    funct7: 7

fn bitfield_rw(raw: u32, next_rd: i64) -> i64:
    var inst = Rv32Instruction.new(raw)
    val old_rd = inst.rd
    inst.rd = next_rd
    return old_rd
"#,
    )
    .unwrap();

    let func = &mir.functions[0];
    let ops: Vec<_> = func.blocks.iter().flat_map(|block| block.instructions.iter()).collect();

    assert!(ops
        .iter()
        .any(|i| matches!(i, MirInst::BinOp { op: BinOp::BitAnd, .. })));
    assert!(ops.iter().any(|i| matches!(
        i,
        MirInst::BinOp {
            op: BinOp::ShiftRight,
            ..
        }
    )));
    assert!(ops.iter().any(|i| matches!(
        i,
        MirInst::BinOp {
            op: BinOp::ShiftLeft,
            ..
        }
    )));
    assert!(ops.iter().any(|i| matches!(i, MirInst::BinOp { op: BinOp::BitOr, .. })));
}

#[test]
fn test_lower_if_statement() {
    let mir = compile_to_mir(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n",
    )
    .unwrap();

    let func = &mir.functions[0];
    // Should have multiple blocks: entry, then, else, merge
    assert!(func.blocks.len() >= 3);

    let entry = func.block(BlockId(0)).unwrap();
    assert!(matches!(entry.terminator, Terminator::Branch { .. }));
}

#[test]
fn test_lower_while_loop() {
    let mir =
        compile_to_mir("fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n")
            .unwrap();

    let func = &mir.functions[0];
    // Should have: entry, condition, body, exit blocks
    assert!(func.blocks.len() >= 4);
}

#[test]
fn test_lower_local_variable() {
    let mir = compile_to_mir("fn test() -> i64:\n    let x: i64 = 5\n    return x\n").unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have LocalAddr and Store for the let
    assert!(entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::LocalAddr { .. })));
    assert!(entry.instructions.iter().any(|i| matches!(i, MirInst::Store { .. })));
}
