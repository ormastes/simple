use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn test_lower_if_statement() {
    let module = parse_and_lower(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::If { .. }));
}

#[test]
fn test_lower_while_loop() {
    let module =
        parse_and_lower("fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n")
            .unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[1], HirStmt::While { .. }));
}

#[test]
fn test_lower_simd_loop_metadata() {
    let module = parse_and_lower(
        "fn count() -> i64:\n    @simd\n    for i in 0..4:\n        pass\n    @simd\n    while false:\n        pass\n    @simd\n    loop:\n        break\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert!(matches!(
        func.body[0],
        HirStmt::For {
            simd_requested: true,
            ..
        }
    ));
    assert!(matches!(
        func.body[1],
        HirStmt::While {
            simd_requested: true,
            ..
        }
    ));
    assert!(matches!(
        func.body[2],
        HirStmt::Loop {
            simd_requested: true,
            ..
        }
    ));
}

/// Regression: multi-statement match arms must keep their leading statements.
/// `lower_match_arm_body` used to discard everything but the trailing
/// expression — `val y = ...` only registered the local without a Let store,
/// so the local stayed uninitialized (stage4 `CompileContext.create` SIGSEGV
/// where a lambda captured the arm-local receiver as nil).
#[test]
fn test_match_arm_leading_statements_are_kept() {
    let module = parse_and_lower(
        "fn pick(mode: i64) -> i64:\n    val r = match mode:\n        case 0:\n            val y = 41\n            y + 1\n        case _:\n            0\n    return r\n",
    )
    .unwrap();

    let func = &module.functions[0];
    let repr = format!("{:?}", func.body[0]);
    assert!(
        repr.contains("Block"),
        "match arm body lost its statement block: {repr}"
    );
    assert!(
        repr.contains("Integer(41)"),
        "match arm `val y = 41` initializer was dropped: {repr}"
    );
}
