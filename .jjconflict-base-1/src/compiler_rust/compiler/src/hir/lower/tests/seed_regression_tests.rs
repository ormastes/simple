//! Regression tests for seed compiler bugs fixed 2026-07-16:
//!
//! - 86e56ca7867 (hir/lower/expr/mod.rs:574-586): qualified `Result.Ok(x)` /
//!   `Option.Some(x)` receivers must lower to static-member/enum construction
//!   (`Global("Result::Ok")` etc.) even when `module.types.lookup("Result")`
//!   misses (builtin generic instantiations are registered unnamed, so
//!   freestanding/entry-closure modules that never lower the enum
//!   declaration never see them in the type registry).
//! - 6b59a8c4bf7 (hir/lower/expr/collections.rs + calls.rs
//!   `lower_struct_init_fields`): struct-init fields must be assigned by
//!   DECLARED field order regardless of source-written order, with missing
//!   fields nil-filled; paren-call and brace-literal forms must agree.

use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;

#[test]
fn unmatched_literal_brace_does_not_consume_later_function_scope() {
    let source = r#"fn open_brace(x: text) -> text:
    " { "

fn main():
    val ob = open_brace("unused")
    val rule = ".a" + ob + "color: red" + " } "
    print("RULE: [" + rule + "]")

main()
"#;
    let module =
        parse_and_lower(source).expect("literal braces must not leak expressions across functions");
    assert!(module
        .functions
        .iter()
        .any(|function| function.name == "open_brace"));
    assert!(module.functions.iter().any(|function| function.name == "main"));
}

// =============================================================================
// #1: Result.Ok / Option.Some qualified-receiver routing (86e56ca7867)
// =============================================================================

#[test]
fn result_ok_receiver_lowers_to_static_enum_construct_without_result_registration() {
    // No `Result` type ever appears in a declaration in this module -- matches
    // freestanding/entry-closure kernel modules that never lower the builtin
    // Result enum, so `module.types.lookup("Result")` misses.
    let module = parse_and_lower("fn make() -> i64:\n    val r = Result.Ok(1)\n    return 0\n").unwrap();
    let function = module.functions.iter().find(|f| f.name == "make").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let binding for Result.Ok(1), got {:?}", function.body[0]);
    };
    let HirExprKind::Call { func: callee, args } = &expr.kind else {
        panic!("expected Call (static enum construct), got {:?}", expr.kind);
    };
    assert_eq!(
        callee.kind,
        HirExprKind::Global("Result::Ok".to_string()),
        "Result.Ok(x) must route through static-member lowering to Global(\"Result::Ok\"), \
         which MIR canonicalizes to MirInst::ResultOk -- NOT a dynamic MethodCallStatic on an \
         unresolved global"
    );
    assert_eq!(args.len(), 1);

    let body = format!("{:?}", function.body);
    assert!(
        !body.contains("method: \"Ok\""),
        "must not degrade to a dynamic method call named \"Ok\" (unresolved-global dispatch): {body}"
    );
}

#[test]
fn option_some_receiver_lowers_to_static_enum_construct_without_option_registration() {
    let module = parse_and_lower("fn make() -> i64:\n    val r = Option.Some(1)\n    return 0\n").unwrap();
    let function = module.functions.iter().find(|f| f.name == "make").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let binding for Option.Some(1), got {:?}", function.body[0]);
    };
    let HirExprKind::Call { func: callee, args } = &expr.kind else {
        panic!("expected Call (static enum construct), got {:?}", expr.kind);
    };
    assert_eq!(
        callee.kind,
        HirExprKind::Global("Option::Some".to_string()),
        "Option.Some(x) must route through static-member lowering to Global(\"Option::Some\")"
    );
    assert_eq!(args.len(), 1);

    let body = format!("{:?}", function.body);
    assert!(
        !body.contains("method: \"Some\""),
        "must not degrade to a dynamic method call named \"Some\": {body}"
    );
}

/// Sibling: unit-variant `Option.None` (no call args) is FIELD ACCESS syntax,
/// not a method call, so it is NOT covered by the 86e56ca7867 method-call
/// routing fix -- `lower_field_access` (access.rs) only synthesizes an
/// unresolved-type static variant global under `lenient_types`. Documents
/// current behavior: with lenient mode on, it still resolves; this pins the
/// existing lenient-fallback contract so a future refactor of either path
/// doesn't silently regress it.
#[test]
fn option_none_unit_variant_resolves_under_lenient_mode() {
    let source = "fn make() -> i64:\n    val r = Option.None\n    return 0\n";
    let mut parser = simple_parser::Parser::new(source);
    let parsed = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    let lowered = lowerer.lower_module(&parsed).expect("lowering must succeed under lenient mode");

    let function = lowered.functions.iter().find(|f| f.name == "make").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let binding for Option.None, got {:?}", function.body[0]);
    };
    assert_eq!(expr.kind, HirExprKind::Global("Option::None".to_string()));
}

/// Sibling: nested generic receivers -- `Result.Ok(Option.Some(1))` -- both
/// qualified calls must route through static-member lowering independently;
/// neither should leak a MethodCallStatic dispatch anywhere in the body.
#[test]
fn nested_result_option_receivers_both_route_through_static_construct() {
    let module = parse_and_lower("fn make() -> i64:\n    val r = Result.Ok(Option.Some(1))\n    return 0\n").unwrap();
    let function = module.functions.iter().find(|f| f.name == "make").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let binding, got {:?}", function.body[0]);
    };
    let HirExprKind::Call { func: outer_callee, args: outer_args } = &expr.kind else {
        panic!("expected outer Call, got {:?}", expr.kind);
    };
    assert_eq!(outer_callee.kind, HirExprKind::Global("Result::Ok".to_string()));
    assert_eq!(outer_args.len(), 1);

    let HirExprKind::Call { func: inner_callee, args: inner_args } = &outer_args[0].kind else {
        panic!("expected nested Call for Option.Some(1), got {:?}", outer_args[0].kind);
    };
    assert_eq!(inner_callee.kind, HirExprKind::Global("Option::Some".to_string()));
    assert_eq!(inner_args.len(), 1);

    let body = format!("{:?}", function.body);
    assert!(
        !body.contains("method: \"Ok\"") && !body.contains("method: \"Some\""),
        "nested Result/Option receivers must not leak dynamic method-call dispatch: {body}"
    );
}

// =============================================================================
// #3: struct-init fields lowered by DECLARED order + nil-fill (6b59a8c4bf7)
// =============================================================================

fn struct_init_fields<'a>(function: &'a HirFunction) -> &'a Vec<HirExpr> {
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let binding, got {:?}", function.body[0]);
    };
    let HirExprKind::StructInit { fields, .. } = &expr.kind else {
        panic!("expected StructInit, got {:?}", expr.kind);
    };
    fields
}

#[test]
fn struct_init_brace_form_lowers_fields_in_declared_order_regardless_of_written_order() {
    let module = parse_and_lower(
        "struct Point:\n    x: i64\n    y: i64\n    z: i64\n\nfn test() -> i64:\n    val p = Point { z: 3, x: 1, y: 2 }\n    return 0\n",
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "test").unwrap();
    let fields = struct_init_fields(function);
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[0].kind, HirExprKind::Integer(1), "declared slot 0 (x) must get the x: 1 value");
    assert_eq!(fields[1].kind, HirExprKind::Integer(2), "declared slot 1 (y) must get the y: 2 value");
    assert_eq!(fields[2].kind, HirExprKind::Integer(3), "declared slot 2 (z) must get the z: 3 value");
}

#[test]
fn struct_init_paren_form_agrees_with_brace_form_on_declared_order() {
    let module = parse_and_lower(
        "struct Point:\n    x: i64\n    y: i64\n    z: i64\n\nfn test() -> i64:\n    val p = Point(z: 3, x: 1, y: 2)\n    return 0\n",
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "test").unwrap();
    let fields = struct_init_fields(function);
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[0].kind, HirExprKind::Integer(1), "paren form must match brace form: declared slot 0 (x)");
    assert_eq!(fields[1].kind, HirExprKind::Integer(2), "paren form must match brace form: declared slot 1 (y)");
    assert_eq!(fields[2].kind, HirExprKind::Integer(3), "paren form must match brace form: declared slot 2 (z)");
}

#[test]
fn struct_init_partial_fields_nil_fill_missing_declared_slots() {
    let module = parse_and_lower(
        "struct Point:\n    x: i64\n    y: i64\n    z: i64\n\nfn test() -> i64:\n    val p = Point { x: 10, z: 30 }\n    return 0\n",
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "test").unwrap();
    let fields = struct_init_fields(function);
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[0].kind, HirExprKind::Integer(10), "x provided");
    assert_eq!(fields[1].kind, HirExprKind::Nil, "y omitted -- must nil-fill, not shift z into slot 1");
    assert_eq!(fields[2].kind, HirExprKind::Integer(30), "z provided, must stay in its own declared slot");
}

/// Sibling: zero explicit fields -- every declared slot must nil-fill (not
/// panic, not leave the fields vector short).
#[test]
fn struct_init_zero_fields_nil_fills_all_declared_slots() {
    let module = parse_and_lower(
        "struct Point:\n    x: i64\n    y: i64\n    z: i64\n\nfn test() -> i64:\n    val p = Point()\n    return 0\n",
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "test").unwrap();
    let fields = struct_init_fields(function);
    assert_eq!(fields.len(), 3, "all 3 declared fields must be present even with zero provided args");
    for (idx, field) in fields.iter().enumerate() {
        assert_eq!(field.kind, HirExprKind::Nil, "slot {idx} must nil-fill when nothing is provided");
    }
}

/// Sibling: all fields provided, all out of declared order (paren form).
#[test]
fn struct_init_all_fields_named_out_of_declared_order() {
    let module = parse_and_lower(
        "struct Widget:\n    a: i64\n    b: i64\n    c: i64\n    d: i64\n\nfn test() -> i64:\n    val w = Widget(d: 4, b: 2, a: 1, c: 3)\n    return 0\n",
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "test").unwrap();
    let fields = struct_init_fields(function);
    assert_eq!(fields.len(), 4);
    assert_eq!(fields[0].kind, HirExprKind::Integer(1), "a");
    assert_eq!(fields[1].kind, HirExprKind::Integer(2), "b");
    assert_eq!(fields[2].kind, HirExprKind::Integer(3), "c");
    assert_eq!(fields[3].kind, HirExprKind::Integer(4), "d");
}
