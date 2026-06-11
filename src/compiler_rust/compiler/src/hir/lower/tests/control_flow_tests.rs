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

#[test]
fn test_untyped_empty_array_specializes_on_first_append() {
    let module = parse_and_lower(
        "class Boxed:\n    value: i64\n\nfn run_one() -> i64:\n    var items = []\n    items.append(Boxed(value: 7))\n    for item in items:\n        return item.value\n    return 0\n",
    )
    .unwrap();

    let func = &module.functions[0];
    let HirStmt::Let { local_index, ty, .. } = &func.body[0] else {
        panic!("expected first statement to be the items binding");
    };
    let HirStmt::Expr(HirExpr {
        kind: HirExprKind::MethodCall { receiver, .. },
        ..
    }) = &func.body[1]
    else {
        panic!("expected second statement to be items.append(...)");
    };
    let HirStmt::For { pattern_local, iterable, .. } = &func.body[2] else {
        panic!("expected third statement to be the items loop");
    };

    assert!(matches!(
        module.types.get(*ty),
        Some(HirType::Array { element, .. }) if *element == TypeId::ANY
    ));
    assert!(matches!(receiver.as_ref().kind, HirExprKind::Local(idx) if idx == *local_index));

    let specialized_local = &func.locals[*local_index];
    assert!(matches!(
        module.types.get(specialized_local.ty),
        Some(HirType::Array { element, .. }) if matches!(module.types.get(*element), Some(HirType::Struct { name, .. }) if name == "Boxed")
    ));
    let loop_local_index = pattern_local.expect("loop local should be recorded");
    let loop_local = &func.locals[loop_local_index];
    assert_eq!(loop_local.name, "item");
    assert!(matches!(
        module.types.get(loop_local.ty),
        Some(HirType::Struct { name, .. }) if name == "Boxed"
    ));
    assert!(matches!(
        module.types.get(iterable.ty),
        Some(HirType::Array { element, .. }) if matches!(module.types.get(*element), Some(HirType::Struct { name, .. }) if name == "Boxed")
    ));
}
