use super::parse_and_lower;
use crate::hir::HirStmt;

#[test]
fn callable_assert_true_and_false_use_assertion_owner() {
    for literal in ["true", "false"] {
        let module = parse_and_lower(&format!("fn probe():\n    assert({literal})\n")).unwrap();
        let body = &module.functions.iter().find(|f| f.name == "probe").unwrap().body;
        assert!(matches!(body.first(), Some(HirStmt::Assert { .. })));
    }
}

#[test]
fn declared_assert_callable_keeps_its_owner() {
    let module = parse_and_lower("fn assert(value: bool):\n    pass\nfn probe():\n    assert(true)\n").unwrap();
    let body = &module.functions.iter().find(|f| f.name == "probe").unwrap().body;
    assert!(matches!(body.first(), Some(HirStmt::Expr(_))));
}
