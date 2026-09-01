//! HIR lowering tests for struct-update spread `..base`.
//!
//! Bug: `doc/08_tracking/bug/struct_spread_paren_form_parses_as_range_2026-08-30.md`.
//!
//! Before this fix HIR discarded the spread outright: `expr/mod.rs` matched
//! `Expr::StructInit { name, fields, .. }` (dropping the `spread` field) and
//! the paren form never even reached HIR as a spread — it arrived as an
//! `Expr::Range`, which lowered to `rt_range(0, <tagged object pointer>)`.
//!
//! Semantics pinned here: explicit field > spread base > declared default,
//! base evaluated EXACTLY ONCE (bound by a `LetIn` temp).

use super::parse_and_lower;
use crate::hir::types::*;

const POINT: &str = "class Point:\n    var x: i64\n    var y: i64\n    var z: i64\n\n";

/// Return the `Let` initializer of the named function's first `let`.
fn first_let_value(module: &HirModule, func_name: &str) -> HirExpr {
    let func = module
        .functions
        .iter()
        .find(|f| f.name == func_name)
        .unwrap_or_else(|| panic!("function `{func_name}` not lowered"));
    func.body
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::Let { value: Some(value), .. } => Some(value.clone()),
            _ => None,
        })
        .expect("let initializer")
}

/// Unwrap the `LetIn` a spread introduces and return `(local_idx, fields)`.
fn spread_init(expr: &HirExpr) -> (usize, Vec<HirExpr>) {
    match &expr.kind {
        HirExprKind::LetIn { local_idx, body, .. } => match &body.kind {
            HirExprKind::StructInit { fields, .. } => (*local_idx, fields.clone()),
            other => panic!("expected StructInit inside LetIn, got {other:?}"),
        },
        other => panic!("expected LetIn (spread base bound once), got {other:?}"),
    }
}

fn is_base_field(expr: &HirExpr, local_idx: usize, index: usize) -> bool {
    match &expr.kind {
        HirExprKind::FieldAccess { receiver, field_index } => {
            *field_index == index && matches!(receiver.kind, HirExprKind::Local(i) if i == local_idx)
        }
        _ => false,
    }
}

#[test]
fn paren_spread_fills_unlisted_fields_from_base() {
    let module = parse_and_lower(&format!(
        "{POINT}fn make(base: Point) -> Point:\n    let p: Point = Point(..base, y: 9)\n    return p\n"
    ))
    .expect("lower ok");

    let value = first_let_value(&module, "make");
    let (local_idx, fields) = spread_init(&value);
    assert_eq!(fields.len(), 3, "all three declared slots must be filled");
    // Declared order is x, y, z. `y` is listed explicitly and must OVERRIDE
    // the base; `x` and `z` come from the base.
    assert!(is_base_field(&fields[0], local_idx, 0), "x should come from base");
    assert!(
        matches!(fields[1].kind, HirExprKind::Integer(9)),
        "explicitly listed y must override the base, got {:?}",
        fields[1].kind
    );
    assert!(is_base_field(&fields[2], local_idx, 2), "z should come from base");
}

#[test]
fn spread_base_is_evaluated_exactly_once() {
    // A side-effecting base must run once, not once per unlisted field.
    let module = parse_and_lower(&format!(
        "{POINT}fn origin() -> Point:\n    return Point(x: 0, y: 0, z: 0)\n\n\
         fn make() -> Point:\n    let p: Point = Point(..origin(), y: 9)\n    return p\n"
    ))
    .expect("lower ok");

    let value = first_let_value(&module, "make");
    let HirExprKind::LetIn { value: bound, .. } = &value.kind else {
        panic!("expected LetIn, got {:?}", value.kind);
    };
    // The call appears exactly once, as the LetIn's bound value.
    assert!(
        matches!(bound.kind, HirExprKind::Call { .. } | HirExprKind::BuiltinCall { .. }),
        "base call must be the bound value, got {:?}",
        bound.kind
    );
    let (local_idx, fields) = spread_init(&value);
    assert!(is_base_field(&fields[0], local_idx, 0));
    assert!(is_base_field(&fields[2], local_idx, 2));
}

#[test]
fn brace_spread_is_no_longer_discarded() {
    // `expr/mod.rs` used to drop `StructInit.spread` on the floor.
    let module = parse_and_lower(&format!(
        "{POINT}fn make(base: Point) -> Point:\n    let p: Point = Point {{ y: 9, ..base }}\n    return p\n"
    ))
    .expect("lower ok");

    let value = first_let_value(&module, "make");
    let (local_idx, fields) = spread_init(&value);
    assert_eq!(fields.len(), 3);
    assert!(is_base_field(&fields[0], local_idx, 0));
    assert!(matches!(fields[1].kind, HirExprKind::Integer(9)));
    assert!(is_base_field(&fields[2], local_idx, 2));
}

#[test]
fn spread_beats_a_declared_field_default() {
    // `..base` means "the rest comes from base" — a class-level `= default`
    // must NOT win over it.
    let module = parse_and_lower(
        "class Cfg:\n    var a: i64 = 7\n    var b: i64 = 8\n\n\
         fn make(base: Cfg) -> Cfg:\n    let c: Cfg = Cfg(..base, b: 1)\n    return c\n",
    )
    .expect("lower ok");

    let value = first_let_value(&module, "make");
    let (local_idx, fields) = spread_init(&value);
    assert!(
        is_base_field(&fields[0], local_idx, 0),
        "a must come from the base, not from its `= 7` default, got {:?}",
        fields[0].kind
    );
    assert!(matches!(fields[1].kind, HirExprKind::Integer(1)));
}

#[test]
fn no_spread_still_lowers_without_a_letin() {
    // Containment: an ordinary construction is untouched by this feature.
    let module = parse_and_lower(&format!(
        "{POINT}fn make() -> Point:\n    let p: Point = Point(x: 1, y: 2, z: 3)\n    return p\n"
    ))
    .expect("lower ok");

    let value = first_let_value(&module, "make");
    assert!(
        matches!(value.kind, HirExprKind::StructInit { .. }),
        "expected a bare StructInit, got {:?}",
        value.kind
    );
}

#[test]
fn ordinary_ranges_still_lower_as_ranges() {
    // The single most important regression guard: `..` is shared with range
    // syntax, and turning real ranges into spreads would be worse than the bug.
    let module = parse_and_lower("fn f():\n    let r = 0..5\n").expect("lower ok");
    let value = first_let_value(&module, "f");
    let repr = format!("{value:?}");
    assert!(
        !repr.contains("StructInit"),
        "a plain range must not become a struct init: {repr}"
    );
}

#[test]
fn spread_in_a_non_constructor_call_is_a_hard_error() {
    // This is the containment for a genuine prefix-range ARGUMENT: it becomes
    // a loud diagnostic instead of `rt_range(0, <object pointer>)`.
    let err = parse_and_lower("fn take(n: i64) -> i64:\n    return n\n\nfn f() -> i64:\n    return take(..n)\n")
        .expect_err("must not lower");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("struct spread"),
        "expected a struct-spread diagnostic, got {msg}"
    );
}

#[test]
fn two_spreads_in_one_construction_are_rejected() {
    let err = parse_and_lower(&format!(
        "{POINT}fn make(a: Point, b: Point) -> Point:\n    return Point(..a, ..b)\n"
    ))
    .expect_err("must not lower");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("at most one"),
        "expected an at-most-one-spread diagnostic, got {msg}"
    );
}
