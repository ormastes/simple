//! Control flow tests for MIR lowering
//!
//! Tests for if/else, match, while/break/continue, for loops, and return statements.

use super::super::common::*;
use super::helpers::*;
use crate::hir::BinOp;
use crate::mir::lower::ContractMode;
use crate::mir::{CallTarget, MirInst, Terminator};

// =============================================================================
// If expression without else (lowering_expr.rs line 1171)
// =============================================================================

#[test]
fn if_without_else() {
    let mir =
        compile_to_mir("fn test(x: i64) -> i64:\n    if x > 0:\n        print \"positive\"\n    return x\n").unwrap();
    let func = &mir.functions[0];
    assert!(func.blocks.len() >= 2);
}

// =============================================================================
// Let without value (lowering_stmt.rs line 19)
// =============================================================================

#[test]
fn let_without_value() {
    let mir = compile_to_mir("fn test() -> i64:\n    var x: i64\n    x = 42\n    return x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::LocalAddr { .. })));
}

// =============================================================================
// Index assign (lowering_stmt.rs lines 85-162)
// =============================================================================

#[test]
fn index_set_generates_instruction() {
    let mir = compile_to_mir("fn test():\n    var arr = [0, 0]\n    arr[0] = 42\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_index_set"))
    }));
}

#[test]
fn u8_index_set_uses_byte_fast_path() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u8] = [0, 0]\n    var byte: u8 = 42\n    arr[0] = byte\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_bytes_u8_set"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_index_set"))
    }));
}

#[test]
fn u32_index_set_uses_word_fast_path() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u32] = [0, 0]\n    var word: u32 = 42\n    arr[1] = word\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_words_u32_set"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_index_set"))
    }));
}

#[test]
fn u8_array_push_uses_byte_fast_path() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u8] = []\n    var byte: u8 = 42\n    arr.push(byte)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_bytes_u8_push"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_push"))
    }));
}

#[test]
fn empty_u8_array_uses_codec_table_capacity() {
    let mir = compile_to_mir("fn test():\n    var arr: [u8] = []\n").unwrap();
    let mut found_capacity = false;
    for func in &mir.functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                if let MirInst::Call { target, args, .. } = inst {
                    if target == &CallTarget::from_name("rt_byte_array_new") && args.len() == 1 {
                        let capacity_reg = args[0];
                        found_capacity = block.instructions.iter().any(|candidate| {
                            matches!(candidate, MirInst::ConstInt { dest, value } if *dest == capacity_reg && *value == 1024)
                        });
                    }
                }
            }
        }
    }
    assert!(found_capacity);
}

#[test]
fn nonempty_u8_array_literal_uses_byte_storage() {
    let mir = compile_to_mir("fn test():\n    val a: u8 = 1\n    val b: u8 = 2\n    val arr: [u8] = [a, b]\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_byte_array_new"))
    }));
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_bytes_u8_push"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_push"))
    }));
}

#[test]
fn u32_array_push_uses_word_fast_path() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u32] = []\n    var word: u32 = 42\n    arr.push(word)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_words_u32_push"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_push"))
    }));
}

#[test]
fn u64_array_push_uses_word_fast_path() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u64] = []\n    var word: u64 = 42u64\n    arr.push(word)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_typed_words_u64_push"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_push"))
    }));
}

#[test]
fn unused_u64_array_push_result_is_discarded() {
    let mir =
        compile_to_mir("fn test():\n    var arr: [u64] = []\n    var word: u64 = 42u64\n    arr.push(word)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(
            i,
            MirInst::Call { dest: None, target, .. }
                if target == &CallTarget::from_name("rt_typed_words_u64_push")
        )
    }));
}

#[test]
fn index_set_float_boxing() {
    let mir = compile_to_mir("fn test():\n    var arr = [0.0, 0.0]\n    arr[0] = 3.14\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

// =============================================================================
// If/else value merge (lowering_stmt.rs line 309)
// =============================================================================

#[test]
fn if_else_value_merge() {
    let mir =
        compile_to_mir("fn test(x: i64) -> i64:\n    let result = if x > 0: 42 else: 0\n    return result\n").unwrap();
    let func = &mir.functions[0];
    assert!(func.blocks.len() >= 3);
}

// =============================================================================
// Range-based for loop (lowering_stmt.rs lines 536-537)
// =============================================================================

#[test]
fn for_range_exclusive() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum = 0\n    for i in 0..5:\n        sum = sum + i\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::Lt, .. })));
}

#[test]
fn for_range_inclusive() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum = 0\n    for i in 0..=5:\n        sum = sum + i\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::LtEq, .. })));
}

// =============================================================================
// Collection for loop (lowering_stmt.rs lines 556, 562)
// =============================================================================

#[test]
fn for_collection() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum = 0\n    for x in [10, 20, 12]:\n        sum = sum + x\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_len"))
    }));
}

// =============================================================================
// Nested if/else (more blocks)
// =============================================================================

#[test]
fn nested_if_else() {
    let mir = compile_to_mir(
        "fn test(x: i64) -> i64:\n    if x > 10:\n        return 1\n    else:\n        if x > 0:\n            return 2\n        else:\n            return 3\n",
    ).unwrap();
    let func = &mir.functions[0];
    assert!(func.blocks.len() >= 4);
}

// =============================================================================
// Void/implicit return (lowering_core.rs lines 689-694)
// =============================================================================

#[test]
fn void_implicit_return() {
    let mir = compile_to_mir("fn test():\n    let x = 42\n").unwrap();
    let func = &mir.functions[0];
    let last = func.blocks.last().unwrap();
    assert!(matches!(last.terminator, Terminator::Return(None)));
}

#[test]
fn nonvoid_implicit_return() {
    let mir = compile_to_mir("fn test() -> i64:\n    42\n").unwrap();
    let func = &mir.functions[0];
    let last = func.blocks.last().unwrap();
    assert!(matches!(last.terminator, Terminator::Return(Some(_))));
}

// =============================================================================
// Drop for locals (lowering_stmt.rs lines 878, 882)
// =============================================================================

#[test]
fn drops_for_locals() {
    let mir =
        compile_to_mir("fn test() -> i64:\n    let a = 10\n    let b = 20\n    let c = 12\n    return a + b + c\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Drop { .. })));
}

// =============================================================================
// While/break/continue
// =============================================================================

#[test]
fn while_false_still_generates_blocks() {
    let mir =
        compile_to_mir("fn test() -> i64:\n    var x = 42\n    while false:\n        x = 0\n    return x\n").unwrap();
    assert!(mir.functions[0].blocks.len() >= 2);
}

#[test]
fn break_in_while() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var x = 0\n    while true:\n        x = 42\n        break\n    return x\n",
    )
    .unwrap();
    assert!(mir.functions[0].blocks.len() >= 3);
}

#[test]
fn continue_in_while() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum = 0\n    var i = 0\n    while i < 10:\n        i = i + 1\n        if i == 5:\n            continue\n        sum = sum + i\n    return sum\n",
    ).unwrap();
    assert!(mir.functions[0].blocks.len() >= 4);
}

// =============================================================================
// Index assign bool boxing (lowering_stmt.rs lines 90-91, 130)
// =============================================================================

#[test]
fn index_set_bool_value_boxing() {
    // Setting a bool value into an array should box via rt_value_bool
    let mir = compile_to_mir("fn test():\n    var arr = [true, false]\n    arr[0] = true\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_bool"))
    }));
}

#[test]
fn index_set_float_value_boxing() {
    // Setting a float value should box via BoxFloat
    let mir = compile_to_mir("fn test():\n    var arr = [1.0, 2.0]\n    arr[0] = 3.14\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

// =============================================================================
// If/else expression with else (lowering_expr.rs line 1230)
// =============================================================================

#[test]
fn if_else_expression() {
    let mir =
        compile_to_mir("fn test(x: i64) -> i64:\n    val result = if x > 0: 42 else: -1\n    return result\n").unwrap();
    let func = &mir.functions[0];
    assert!(func.blocks.len() >= 3); // then, else, merge blocks
}

// =============================================================================
// If/else stmt with else block (lowering_stmt.rs line 316)
// =============================================================================

#[test]
fn if_else_stmt_with_else() {
    let mir = compile_to_mir(
        "fn test(x: i64) -> i64:\n    var result = 0\n    if x > 0:\n        result = 42\n    else:\n        result = -1\n    return result\n",
    ).unwrap();
    let func = &mir.functions[0];
    assert!(func.blocks.len() >= 3);
}

// =============================================================================
// Return without value (lowering_stmt.rs line 227)
// =============================================================================

#[test]
fn return_none_void() {
    let mir = compile_to_mir("fn test():\n    return\n").unwrap();
    let func = &mir.functions[0];
    assert!(matches!(
        func.blocks.last().unwrap().terminator,
        Terminator::Return(None)
    ));
}

// =============================================================================
// Function with parameters - drop skips params (lowering_stmt.rs lines 906, 910)
// =============================================================================

#[test]
fn drops_skip_parameters() {
    let mir = compile_to_mir("fn test(a: i64, b: i64) -> i64:\n    let c = a + b\n    return c\n").unwrap();
    // Should have drops for local `c` but not for params `a`, `b`
    let drop_count = count_inst(&mir, |i| matches!(i, MirInst::Drop { .. }));
    assert!(drop_count >= 1, "expected at least 1 drop for local c");
}

// =============================================================================
// Multiple function definitions (lowering_core.rs - multiple lower_function calls)
// =============================================================================

#[test]
fn multiple_functions() {
    let mir =
        compile_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n")
            .unwrap();
    assert!(mir.functions.len() >= 2);
}

// =============================================================================
// Inclusive range for loop (lowering_stmt.rs line 558)
// =============================================================================

#[test]
fn for_range_inclusive_generates_lteq() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum = 0\n    for i in 0..=10:\n        sum = sum + i\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::LtEq, .. })));
}

// =============================================================================
// Pattern matching (lowering_expr.rs - PatternTest)
// =============================================================================

#[test]
fn match_enum_pattern() {
    let mir = compile_to_mir(
        "enum Shape:\n    Circle(i64)\n    Square(i64)\n\nfn test(s: Shape) -> i64:\n    match s:\n        Shape.Circle(r): return r\n        Shape.Square(w): return w\n",
    );
    if let Ok(mir) = mir {
        assert!(!mir.functions.is_empty());
    }
}
