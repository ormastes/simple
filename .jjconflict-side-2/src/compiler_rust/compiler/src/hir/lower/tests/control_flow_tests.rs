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
