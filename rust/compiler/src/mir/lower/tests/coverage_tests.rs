//! Coverage instrumentation tests for MIR lowering (#674)

use super::common::*;
use crate::mir::{MirInst, Terminator};
use crate::mir::lower::{lower_to_mir_with_coverage, MirLowerResult};
use crate::hir;
use simple_parser::Parser;

/// Helper to compile with coverage enabled
fn compile_with_coverage(source: &str) -> MirLowerResult<crate::mir::function::MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    lower_to_mir_with_coverage(&hir_module, true)
}

#[test]
fn test_if_statement_decision_probe() {
    let source = r#"
fn test(x: i64) -> i64:
    if x > 0:
        return 1
    return 0
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have a DecisionProbe for the if condition
    let has_decision_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
    });

    assert!(has_decision_probe, "If statement should have decision probe");
}

#[test]
fn test_while_loop_decision_probe() {
    let source = r#"
fn test(x: i64) -> i64:
    var count = 0
    while count < x:
        count = count + 1
    return count
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have a DecisionProbe for the while condition
    let has_decision_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
    });

    assert!(has_decision_probe, "While loop should have decision probe");
}

#[test]
fn test_compound_boolean_condition_probes() {
    let source = r#"
fn test(a: bool, b: bool) -> bool:
    return a and b
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have ConditionProbes for each operand and a DecisionProbe for the result
    let condition_probe_count = func
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter(|inst| matches!(inst, MirInst::ConditionProbe { .. }))
        .count();

    let decision_probe_count = func
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
        .count();

    // 2 ConditionProbes (one for each operand) + 1 DecisionProbe (for the result)
    assert_eq!(
        condition_probe_count, 2,
        "Should have 2 condition probes for and operands"
    );
    assert!(
        decision_probe_count >= 1,
        "Should have at least 1 decision probe for and result"
    );
}

#[test]
fn test_or_expression_condition_probes() {
    let source = r#"
fn test(a: bool, b: bool) -> bool:
    return a or b
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have ConditionProbes for each operand
    let condition_probe_count = func
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter(|inst| matches!(inst, MirInst::ConditionProbe { .. }))
        .count();

    assert_eq!(
        condition_probe_count, 2,
        "Should have 2 condition probes for or operands"
    );
}

#[test]
fn test_function_entry_path_probe() {
    let source = r#"
fn test() -> i64:
    return 42
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have a PathProbe at function entry
    let has_path_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::PathProbe { .. }))
    });

    assert!(has_path_probe, "Function should have entry path probe");
}

#[test]
fn test_assert_decision_probe() {
    let source = r#"
fn test(x: i64):
    assert x > 0
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have a DecisionProbe for the assert condition
    let has_decision_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
    });

    assert!(has_decision_probe, "Assert should have decision probe");
}

#[test]
fn test_no_probes_without_coverage() {
    // Use the regular compile_to_mir which has coverage disabled
    let source = r#"
fn test(x: i64) -> i64:
    if x > 0:
        return 1
    return 0
"#;
    let mir = compile_to_mir(source).unwrap();
    let func = &mir.functions[0];

    // Should NOT have any coverage probes
    let has_decision_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
    });

    let has_condition_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::ConditionProbe { .. }))
    });

    let has_path_probe = func.blocks.iter().any(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::PathProbe { .. }))
    });

    assert!(!has_decision_probe, "Should NOT have decision probe without coverage");
    assert!(!has_condition_probe, "Should NOT have condition probe without coverage");
    assert!(!has_path_probe, "Should NOT have path probe without coverage");
}

#[test]
fn test_nested_conditions_coverage() {
    let source = r#"
fn test(x: i64, y: i64) -> i64:
    if x > 0:
        if y > 0:
            return 1
    return 0
"#;
    let mir = compile_with_coverage(source).unwrap();
    let func = &mir.functions[0];

    // Should have 2 DecisionProbes (one for each if)
    let decision_probe_count = func
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter(|inst| matches!(inst, MirInst::DecisionProbe { .. }))
        .count();

    assert_eq!(decision_probe_count, 2, "Should have 2 decision probes for nested ifs");
}
