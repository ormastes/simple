//! Contract lowering tests

use super::common::*;
use simple_compiler::mir::{BlockId, ContractKind, MirInst};

#[test]
fn test_lower_function_with_precondition() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have a ContractCheck instruction for the precondition
    assert!(entry.instructions.iter().any(|i| matches!(
        i,
        MirInst::ContractCheck {
            kind: ContractKind::Precondition,
            ..
        }
    )));
}

#[test]
fn test_lower_function_with_postcondition() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn abs_value(x: i64) -> i64:\n    out(ret):\n        ret >= 0\n    return x\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];

    // Should have a ContractCheck instruction for the postcondition somewhere
    // Check all blocks for postcondition checks
    let has_postcondition_check = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(
                i,
                MirInst::ContractCheck {
                    kind: ContractKind::Postcondition,
                    ..
                }
            )
        })
    });
    assert!(has_postcondition_check, "Should have postcondition check");
}

#[test]
fn test_lower_function_with_invariant() {
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn test_invariant(x: i64) -> i64:\n    invariant:\n        x >= 0\n    return x + 1\n";
    let mir = compile_to_mir(source).unwrap();

    let func = &mir.functions[0];

    // Should have InvariantEntry and InvariantExit checks
    let has_entry = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(
                i,
                MirInst::ContractCheck {
                    kind: ContractKind::InvariantEntry,
                    ..
                }
            )
        })
    });
    let has_exit = func.blocks.iter().any(|block| {
        block.instructions.iter().any(|i| {
            matches!(
                i,
                MirInst::ContractCheck {
                    kind: ContractKind::InvariantExit,
                    ..
                }
            )
        })
    });
    assert!(has_entry, "Should have invariant entry check");
    assert!(has_exit, "Should have invariant exit check");
}
