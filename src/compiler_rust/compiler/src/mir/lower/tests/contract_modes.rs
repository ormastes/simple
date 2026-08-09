//! Contract mode tests (CTR-040 to CTR-043)

use super::common::*;
use crate::mir::{BlockId, ContractKind, ContractMode, MirInst};

#[test]
fn test_contract_mode_off_no_checks() {
    // With ContractMode::Off, no contract checks should be emitted
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Off).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should NOT have any ContractCheck instructions
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { .. }));
    assert!(!has_contract_check, "ContractMode::Off should not emit contract checks");
}

#[test]
fn test_contract_mode_boundary_public_function() {
    // With ContractMode::Boundary, public functions should have contract checks
    let source = "pub fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have ContractCheck for public function
    let has_contract_check = entry.instructions.iter().any(|i| {
        matches!(
            i,
            MirInst::ContractCheck {
                kind: ContractKind::Precondition,
                ..
            }
        )
    });
    assert!(
        has_contract_check,
        "ContractMode::Boundary should emit checks for public functions"
    );
}

#[test]
fn test_contract_mode_boundary_private_function() {
    // With ContractMode::Boundary, private functions should NOT have contract checks
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should NOT have ContractCheck for private function
    let has_contract_check = entry
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::ContractCheck { .. }));
    assert!(
        !has_contract_check,
        "ContractMode::Boundary should not emit checks for private functions"
    );
}

#[test]
fn test_contract_mode_all_checks_all_functions() {
    // With ContractMode::All (default), all functions should have contract checks
    let source = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    return a / b\n";
    let mir = compile_to_mir_with_mode(source, ContractMode::All).unwrap();

    let func = &mir.functions[0];
    let entry = func.block(BlockId(0)).unwrap();

    // Should have ContractCheck for all functions
    let has_contract_check = entry.instructions.iter().any(|i| {
        matches!(
            i,
            MirInst::ContractCheck {
                kind: ContractKind::Precondition,
                ..
            }
        )
    });
    assert!(
        has_contract_check,
        "ContractMode::All should emit checks for all functions"
    );
}

#[test]
fn test_contract_mode_from_str() {
    assert_eq!(ContractMode::from_str("off"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("none"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("boundary"), Some(ContractMode::Boundary));
    assert_eq!(ContractMode::from_str("public"), Some(ContractMode::Boundary));
    assert_eq!(ContractMode::from_str("all"), Some(ContractMode::All));
    assert_eq!(ContractMode::from_str("on"), Some(ContractMode::All));
    assert_eq!(ContractMode::from_str("test"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("debug"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("OFF"), Some(ContractMode::Off));
    assert_eq!(ContractMode::from_str("TEST"), Some(ContractMode::Test));
    assert_eq!(ContractMode::from_str("invalid"), None);
}

#[test]
fn test_contract_mode_as_str() {
    assert_eq!(ContractMode::Off.as_str(), "off");
    assert_eq!(ContractMode::Boundary.as_str(), "boundary");
    assert_eq!(ContractMode::All.as_str(), "all");
    assert_eq!(ContractMode::Test.as_str(), "test");
}

#[test]
fn test_contract_mode_test_has_rich_diagnostics() {
    // CTR-043: Test mode should have rich diagnostics
    assert!(ContractMode::Test.has_rich_diagnostics());
    assert!(!ContractMode::All.has_rich_diagnostics());
    assert!(!ContractMode::Boundary.has_rich_diagnostics());
    assert!(!ContractMode::Off.has_rich_diagnostics());
}

#[test]
fn test_contract_mode_checks_all() {
    // CTR-043: Test mode should check all contracts like All mode
    assert!(ContractMode::Test.checks_all());
    assert!(ContractMode::All.checks_all());
    assert!(!ContractMode::Boundary.checks_all());
    assert!(!ContractMode::Off.checks_all());
}

#[test]
fn test_contract_mode_default_is_all() {
    assert_eq!(ContractMode::default(), ContractMode::All);
}

#[test]
fn test_di_config_parsed_and_stored_in_mir() {
    // DI injection for function calls is handled at HIR level, not MIR call sites
    // (MIR-level injection was removed to avoid signature mismatches).
    // This test verifies that DI config is parsed and the @inject function is lowered
    // correctly, with main calling use_num directly.
    let source = r#"
@inject
fn use_num(x: i64) -> i64:
    return x

fn make_num() -> i64:
    return 42

fn main() -> i64:
    return use_num()
"#;

    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(i64) }", impl = "make_num", scope = "Transient", priority = 10 }
]
"#;

    let mir = compile_to_mir_with_di(source, di_toml).expect("lower with di");
    let main_fn = mir
        .functions
        .iter()
        .find(|func| func.name == "main")
        .expect("main function");

    // main should have a call to use_num (DI resolution happens at HIR level, not MIR call sites)
    let has_use_num_call = main_fn.blocks.iter().any(|block| {
        block
            .instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Call { target, .. } if target.name() == "use_num"))
    });
    assert!(has_use_num_call, "expected call to use_num in main");

    // Verify use_num and make_num functions were lowered
    assert!(
        mir.functions.iter().any(|f| f.name == "use_num"),
        "use_num should be lowered"
    );
    assert!(
        mir.functions.iter().any(|f| f.name == "make_num"),
        "make_num should be lowered"
    );
}
