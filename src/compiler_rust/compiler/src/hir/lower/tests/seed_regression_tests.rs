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
fn stage2_result_projection_map_filter_preserves_checked_result_and_output_owner() {
    let source = concat!(
        "struct Decoy:\n    filler: i64\n    kind: text\n\n",
        "struct Input:\n    kind: i64\n\n",
        "struct Output:\n    kind: i64\n\n",
        "fn make() -> Result<[Input], text>:\n    Ok([Input(kind: 7)])\n\n",
        "fn probe() -> i64:\n",
        "    make().ok().unwrap().filter(\\item: item.kind > 0).map(\\item: Output(kind: item.kind))[0].kind\n",
    );
    let module = parse_and_lower(source).expect("combined Result and collection lowering");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert_eq!(body.matches("rt_enum_payload").count(), 1, "{body}");
    assert!(body.contains("rt_enum_check_variant"), "{body}");
    assert!(body.contains("rt_unwrap_or_trap"), "wrong Result variant must trap: {body}");
    assert!(!body.contains("field_index: 1"), "Decoy cannot provide a field: {body}");
    let HirStmt::Expr(result) = function.body.last().unwrap() else { panic!("expected expression") };
    assert_eq!(result.ty, TypeId::I64);
}

#[test]
fn stage2_nullable_unwrap_evaluates_receiver_once_and_traps_canonical_none() {
    let source = "enum UserKind:\n    Ok(value: i64)\n    Err(value: text)\n    None\n\nfn make() -> UserKind?:\n    nil\n\nfn probe() -> UserKind:\n    make().unwrap()\n";
    let module = parse_and_lower(source).expect("nullable enum lowering");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let HirStmt::Expr(result) = function.body.last().unwrap() else { panic!("expected expression") };
    assert_eq!(module.types.get_type_name(result.ty), Some("UserKind"));
    let HirExprKind::LetIn { local_idx, value, body } = &result.kind else { panic!("receiver once") };
    assert!(format!("{value:?}").contains("Global(\"make\")"));
    let HirExprKind::If { condition, then_branch, else_branch: Some(present) } = &body.kind else { panic!("absence guard") };
    for (expr, expected) in [(condition.as_ref(), "rt_is_none"), (present.as_ref(), "rt_unwrap_or_self")] {
        let HirExprKind::BuiltinCall { name, args } = &expr.kind else { panic!("expected builtin") };
        assert_eq!(name, expected);
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0].kind, HirExprKind::Local(index) if index == *local_idx));
    }
    let HirExprKind::BuiltinCall { name, args } = &then_branch.kind else { panic!("checked absence") };
    assert_eq!(name, "rt_unwrap_or_trap");
    let HirExprKind::BuiltinCall { name, args } = &args[0].kind else { panic!("canonical None constructor") };
    assert_eq!(name, "rt_enum_new");
    assert!(matches!(args[0].kind, HirExprKind::Integer(1)));
    assert!(matches!(args[1].kind, HirExprKind::Integer(tag) if tag == simple_runtime::value::hash_variant_discriminant("None") as i64));
    assert!(matches!(args[2].kind, HirExprKind::Nil));
    assert_eq!(present.ty, result.ty);
    assert!(!format!("{result:?}").contains("rt_enum_payload"));
}

#[test]
fn stage2_indexed_struct_field_keeps_declared_element_owner() {
    let source = "struct Decoy:\n    filler: i64\n    action_id: i64\n\nstruct Runtime:\n    action_id: text\n    state: i64\n\nstruct Coordinator:\n    runtime: [Runtime]\n\nfn probe(coordinator: Coordinator, index: i64) -> text:\n    coordinator.runtime[index].action_id\n";
    let module = parse_and_lower(source).expect("indexed field must use array element owner");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(
        body.contains("field_index: 0"),
        "Runtime.action_id is slot zero: {body}"
    );
    assert!(
        !body.contains("field_index: 1"),
        "Decoy.action_id must not supply the slot: {body}"
    );
}

#[test]
fn stage2_array_sort_callback_uses_both_declared_element_types() {
    let source = "struct Decoy:\n    filler: i64\n    span: i64\n\nstruct Span:\n    start: i64\n\nstruct Item:\n    span: Span\n\nfn array_sort_by(items: [Item], comparator: i64) -> [Item]:\n    items\n\nfn probe(items: [Item]) -> [Item]:\n    array_sort_by(items, \\a, b: if a.span.start < b.span.start: -1 else: 1)\n";
    let module = parse_and_lower(source).expect("two-parameter sort callback must lower");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Item.span is slot zero: {body}");
    assert!(
        !body.contains("field_index: 1"),
        "Decoy.span must not supply a slot: {body}"
    );
}

#[test]
fn stage2_nullable_unwrap_field_uses_pointee_owner() {
    let source = "struct Decoy:\n    filler: i64\n    kind: text\n\nstruct Payload:\n    kind: i64\n\nfn probe(value: Payload?) -> i64:\n    val unwrapped = value.unwrap()\n    unwrapped.kind\n";
    let module = parse_and_lower(source).expect("nullable unwrap must retain payload type");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Payload.kind is slot zero: {body}");
    assert!(
        !body.contains("field_index: 1"),
        "Decoy.kind must not supply a slot: {body}"
    );
}

#[test]
fn stage2_nullable_user_enum_unwrap_keeps_enum_not_first_variant_payload() {
    let source = "enum UserKind:\n    First(value: i64)\n    Second\n\nfn probe(value: UserKind?) -> UserKind:\n    value.unwrap()\n";
    let module = parse_and_lower(source).expect("nullable user enum unwrap must lower");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(
        body.contains("rt_unwrap_or_self") && body.contains("rt_is_none") && body.contains("rt_unwrap_or_trap"),
        "nullable user enum must unwrap only its outer envelope: {body}"
    );
    assert!(!body.contains("rt_enum_payload"), "must not project First payload: {body}");
}

#[test]
fn stage2_named_map_callback_uses_function_return_not_function_value() {
    let source = "struct Decoy:\n    filler: i64\n    priority: text\n\nstruct Rule:\n    priority: i64\n\nstruct Selected:\n    priority: i64\n\nfn select(rule: Rule) -> Selected:\n    Selected(priority: rule.priority)\n\nfn probe(rules: [Rule]) -> i64:\n    rules.map(select)[0].priority\n";
    let module = parse_and_lower(source).expect("named map callback must lower");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Selected.priority is slot zero: {body}");
    assert!(!body.contains("field_index: 1"), "Decoy.priority must not supply a slot: {body}");
}

#[test]
fn stage2_nested_numbered_map_placeholder_keeps_input_owner() {
    let source = "struct Decoy:\n    filler: i64\n    priority: text\n\nstruct Rule:\n    priority: i64\n\nstruct Selected:\n    priority: i64\n\nfn probe(rules: [Rule]) -> [Selected]:\n    rules.map(Selected(priority: _1.priority))\n";
    let module = parse_and_lower(source).expect("nested numbered placeholder must lower");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Rule.priority is slot zero: {body}");
    assert!(!body.contains("field_index: 1"), "Decoy.priority must not supply a slot: {body}");
}

#[test]
fn stage2_map_placeholder_type_field_keeps_input_owner() {
    let source = "struct Decoy:\n    filler: i64\n    type_: text\n\nstruct Param:\n    type_: i64\n\nfn probe(params: [Param]) -> [i64]:\n    params.map(_.type_)\n";
    let module = parse_and_lower(source).expect("type_ placeholder must lower");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Param.type_ is slot zero: {body}");
    assert!(!body.contains("field_index: 1"), "Decoy.type_ must not supply a slot: {body}");
}

#[test]
fn stage2_map_placeholder_uses_collection_element_owner() {
    let source = "struct Decoy:\n    filler: i64\n    priority: text\n\nstruct Rule:\n    priority: i64\n\nfn probe(rules: [Rule]) -> [i64]:\n    rules.map(_.priority)\n";
    let module = parse_and_lower(source).expect("map placeholder must use array element owner");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let body = format!("{:?}", function.body);
    assert!(body.contains("field_index: 0"), "Rule.priority is slot zero: {body}");
    assert!(
        !body.contains("field_index: 1"),
        "Decoy.priority must not supply a slot: {body}"
    );
}

// ---------------------------------------------------------------------------
// jit_is_some_is_none_method_dispatch_gap_2026-08-17 (silent-wrong-value shape)
//
// `.is_some()` / `.is_none()` on a flat-nullable `T?`
// (`HirType::Pointer { inner: T }`) was typed ANY. With an ANY result MIR
// carries no boxing, and the Cranelift arm hands `rt_is_some`'s RAW C bool
// straight to `rt_println_value`: raw `1` is `0b001` = TAG_HEAP and renders
// `nil`, raw `0` collides with boxed integer zero and renders `0`. Measured on
// the JIT lane before the fix: `nil / 0 / 0 / nil` where the interpreter says
// `true / false / false / true`.
// ---------------------------------------------------------------------------

/// Type of the tail `return <recv>.<method>()` expression in `fn_name`.
fn tail_method_call_ty(module: &HirModule, fn_name: &str, method_name: &str) -> Option<TypeId> {
    let function = module.functions.iter().find(|f| f.name == fn_name)?;
    function.body.iter().find_map(|stmt| match stmt {
        HirStmt::Return(Some(expr)) => match &expr.kind {
            HirExprKind::MethodCall { method, .. } if method == method_name => Some(expr.ty),
            _ => None,
        },
        _ => None,
    })
}

#[test]
fn flat_nullable_presence_predicates_are_bool_not_any() {
    // `is_ok`/`is_err` are deliberately absent: their receivers are genuine
    // `Result` ENUMs, handled earlier by `lower_builtin_method_call`, and were
    // measured correct on both engines before and after this change.
    for method in ["is_some", "is_none"] {
        let source = format!(
            "fn produce() -> i64?:\n    return 7\n\nfn probe() -> bool:\n    val a = produce()\n    return a.{}()\n",
            method
        );
        let module = parse_and_lower(&source).expect("flat-nullable presence predicate must lower");
        assert_eq!(
            tail_method_call_ty(&module, "probe", method),
            Some(TypeId::BOOL),
            ".{}() on a flat-nullable T? must be typed BOOL; ANY leaves the JIT's raw \
             rt_is_some result unboxed and it renders as nil/0",
            method
        );
    }
}

#[test]
fn presence_predicate_bool_typing_does_not_leak_to_other_receivers() {
    // A user-declared `is_some` returning something else, on a receiver that is
    // NOT a flat-nullable pointer, must keep its own type — the rule is gated on
    // `HirType::Pointer`, which a struct receiver is not.
    let source = "class Boxy:\n    var n: i64\n\n    fn is_some() -> i64:\n        return 7\n\nfn probe() -> i64:\n    val b = Boxy(n: 1)\n    return b.is_some()\n";
    let module = parse_and_lower(source).expect("struct receiver must lower");
    let ty = tail_method_call_ty(&module, "probe", "is_some");
    assert_ne!(
        ty,
        Some(TypeId::BOOL),
        "a user-declared is_some on a non-nullable receiver must not be forced to BOOL"
    );
}

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
    let module = parse_and_lower(source).expect("literal braces must not leak expressions across functions");
    assert!(module.functions.iter().any(|function| function.name == "open_brace"));
    assert!(module.functions.iter().any(|function| function.name == "main"));
}

#[test]
fn path_typed_string_lowers_to_path_struct_instead_of_text() {
    let source = r#"class Path:
    path: text

fn make_path() -> Path:
    val path = "config/app.toml"_path
    path
"#;
    let module = parse_and_lower(source).expect("_path must lower through the Path constructor");
    let function = module.functions.iter().find(|f| f.name == "make_path").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = function.body[0]
    else {
        panic!("expected let-bound Path construction, got {:?}", function.body[0]);
    };
    let HirExprKind::StructInit { fields, .. } = &expr.kind else {
        panic!("expected Path StructInit, got {:?}", expr.kind);
    };
    assert_eq!(fields.len(), 1);
    assert_eq!(fields[0].kind, HirExprKind::String("config/app.toml".to_string()));
    assert_ne!(expr.ty, TypeId::STRING, "_path suffix must not collapse to text");
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
    let lowered = lowerer
        .lower_module(&parsed)
        .expect("lowering must succeed under lenient mode");

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
    let HirExprKind::Call {
        func: outer_callee,
        args: outer_args,
    } = &expr.kind
    else {
        panic!("expected outer Call, got {:?}", expr.kind);
    };
    assert_eq!(outer_callee.kind, HirExprKind::Global("Result::Ok".to_string()));
    assert_eq!(outer_args.len(), 1);

    let HirExprKind::Call {
        func: inner_callee,
        args: inner_args,
    } = &outer_args[0].kind
    else {
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

/// A declared generic `Result<T, E>` local must retain its enum identity until
/// `.ok` / `.err` projection lowering.  The Windows seed previously erased the
/// local to `i64`, then treated `.ok` as a struct property and dropped the JIT
/// module before the interpreter attempted an enum-to-int conversion.
#[test]
fn annotated_result_local_projects_ok_payload() {
    let source = "fn declared_ok(value: i64) -> Result<i64, text>:\n    Ok(value)\n\nfn main() -> i64:\n    val declared: Result<i64, text> = declared_ok(41)\n    val inferred = declared.ok\n    inferred + 1\n";
    let module = parse_and_lower(source).expect("annotated Result.ok must lower");
    let function = module.functions.iter().find(|f| f.name == "main").unwrap();
    let HirStmt::Let {
        value: Some(expr), ty, ..
    } = &function.body[1]
    else {
        panic!("expected projected Result.ok binding, got {:?}", function.body[1]);
    };
    assert_eq!(*ty, TypeId::I64, "Result.ok must retain its declared payload type");
    assert!(
        matches!(expr.kind, HirExprKind::If { .. }),
        "Result.ok must lower to discriminant-guarded payload projection, got {:?}",
        expr.kind
    );
}

#[test]
fn array_index_declared_element_keeps_field_layout() {
    let source = concat!(
        "struct Action:\n",
        "    pad: i64\n",
        "    priority: i64\n",
        "    action_id: text\n",
        "\n",
        "struct Decoy:\n",
        "    action_id: i64\n",
        "\n",
        "fn probe() -> text:\n",
        "    var ready: [Action] = [Action(pad: 0, priority: 1, action_id: \"go\")]\n",
        "    return ready[0].action_id\n",
    );
    let module = parse_and_lower(source).expect("array index must retain Action owner");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    assert!(matches!(
        function.body.last(),
        Some(HirStmt::Return(Some(HirExpr {
            kind: HirExprKind::FieldAccess { field_index: 2, .. },
            ty: TypeId::STRING,
        })))
    ));
}

#[test]
fn array_map_placeholder_uses_declared_element_field_layout() {
    let source = concat!(
        "struct Param:\n",
        "    pad: i64\n",
        "    type_: text\n",
        "\n",
        "struct Decoy:\n",
        "    type_: i64\n",
        "\n",
        "fn probe(params: [Param]):\n",
        "    params.map(_.type_)\n",
    );
    let module = parse_and_lower(source).expect("map placeholder must inherit array element type");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let Some(HirStmt::Expr(HirExpr {
        kind: HirExprKind::MethodCall { args, .. },
        ..
    })) = function.body.last()
    else {
        panic!("expected map call, got {:?}", function.body.last());
    };
    let Some(HirExpr {
        kind: HirExprKind::Lambda { params, body, .. },
        ..
    }) = args.first()
    else {
        panic!("expected placeholder lambda, got {args:?}");
    };
    assert_eq!(module.types.get_type_name(params[0].1), Some("Param"));
    assert!(matches!(body.kind, HirExprKind::FieldAccess { field_index: 1, .. }));
    assert_eq!(body.ty, TypeId::STRING);
}

#[test]
fn result_ok_call_unwrap_retains_nominal_payload_field_layout() {
    let source = concat!(
        "struct Outcome:\n",
        "    pad: i64\n",
        "    transformed: i64\n",
        "\n",
        "impl Outcome:\n",
        "    fn unwrap() -> text:\n",
        "        \"hostile\"\n",
        "\n",
        "struct Decoy:\n",
        "    transformed: bool\n",
        "\n",
        "fn make() -> Result<Outcome, text>:\n",
        "    Ok(Outcome(pad: 1, transformed: 7))\n",
        "\n",
        "fn probe() -> i64:\n",
        "    val typed_result = make()\n",
        "    val typed_outcome = typed_result.ok().unwrap()\n",
        "    typed_outcome.transformed\n",
    );
    let module = parse_and_lower(source).expect("Result.ok().unwrap() must keep Outcome owner");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let owner = function
        .locals
        .iter()
        .find(|local| local.name == "typed_outcome")
        .unwrap();
    assert_eq!(module.types.get_type_name(owner.ty), Some("Outcome"));
    let HirStmt::Let {
        value: Some(projected), ..
    } = &function.body[1]
    else {
        panic!("expected typed_outcome binding, got {:?}", function.body[1]);
    };
    let HirExprKind::LetIn { body, .. } = &projected.kind else {
        panic!("Result.ok().unwrap() must bind the Result once: {projected:?}");
    };
    let HirExprKind::If {
        condition,
        then_branch,
        else_branch: Some(else_branch),
    } = &body.kind
    else {
        panic!("Result.ok().unwrap() must check the outer variant: {body:?}");
    };
    assert!(format!("{condition:?}").contains("rt_enum_check_variant"));
    assert!(matches!(then_branch.kind, HirExprKind::BuiltinCall { ref name, .. } if name == "rt_enum_payload"));
    assert!(format!("{else_branch:?}").contains("rt_unwrap_or_trap"));
    assert!(!format!("{projected:?}").contains("method: \"unwrap\""));
    assert!(matches!(
        function.body.last(),
        Some(HirStmt::Expr(HirExpr {
            kind: HirExprKind::FieldAccess { field_index: 1, .. },
            ty: TypeId::I64,
        }))
    ));
}

#[test]
fn result_ok_err_methods_return_options_and_guard_wrong_variant() {
    let source = concat!(
        "fn good() -> Result<i64, text>:\n    Ok(7)\n\n",
        "fn bad() -> Result<i64, text>:\n    Err(\"no\")\n\n",
        "fn probe() -> bool:\n",
        "    val present = good().ok()\n",
        "    val absent = bad().ok()\n",
        "    val error = bad().err()\n",
        "    present.is_some() and absent.is_none() and error.is_some()\n",
    );
    let module = parse_and_lower(source).expect("Result methods must lower to Option projections");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    for stmt in function.body.iter().take(3) {
        let HirStmt::Let {
            value: Some(projected), ..
        } = stmt
        else {
            panic!("expected projection: {stmt:?}")
        };
        assert_eq!(module.types.get_type_name(projected.ty), Some("Option"));
        let HirExprKind::LetIn { body, .. } = &projected.kind else {
            panic!("receiver must be evaluated once: {projected:?}")
        };
        let HirExprKind::If {
            condition,
            then_branch,
            else_branch: Some(else_branch),
        } = &body.kind
        else {
            panic!("projection must guard the outer Result: {body:?}")
        };
        let check = format!("{condition:?}");
        assert!(
            check.contains("rt_enum_check_variant") && check.contains("Integer(2)"),
            "{check}"
        );
        assert!(format!("{then_branch:?}").contains("Option::Some"));
        assert!(format!("{else_branch:?}").contains("Option::None"));
    }
}

#[test]
fn nested_enum_result_projection_unwraps_only_outer_result() {
    let source = concat!(
        "fn make() -> Result<Option<i64>, text>:\n    Ok(Option.Some(11))\n\n",
        "fn probe() -> Option<i64>:\n    make().ok().unwrap()\n",
    );
    let module = parse_and_lower(source).expect("nested Option payload must remain intact");
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let HirStmt::Expr(projected) = function.body.last().unwrap() else {
        panic!("expected expression")
    };
    let body = format!("{projected:?}");
    assert_eq!(
        body.matches("rt_enum_payload").count(),
        1,
        "nested payload must not be extracted twice: {body}"
    );
    assert_eq!(module.types.get_type_name(projected.ty), Some("Option"));
}

#[test]
fn annotated_result_local_projects_err_payload() {
    let source = "fn declared_err() -> Result<i64, text>:\n    Err(\"provider-error\")\n\nfn main() -> text:\n    val declared: Result<i64, text> = declared_err()\n    return declared.err\n";
    let module = parse_and_lower(source).expect("annotated Result.err must lower");
    let function = module.functions.iter().find(|f| f.name == "main").unwrap();
    let HirStmt::Return(Some(expr)) = &function.body[1] else {
        panic!("expected projected Result.err return, got {:?}", function.body[1]);
    };
    assert_eq!(
        expr.ty,
        TypeId::STRING,
        "Result.err must retain its declared payload type"
    );
    assert!(matches!(expr.kind, HirExprKind::If { .. }));
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
    assert_eq!(
        fields[0].kind,
        HirExprKind::Integer(1),
        "declared slot 0 (x) must get the x: 1 value"
    );
    assert_eq!(
        fields[1].kind,
        HirExprKind::Integer(2),
        "declared slot 1 (y) must get the y: 2 value"
    );
    assert_eq!(
        fields[2].kind,
        HirExprKind::Integer(3),
        "declared slot 2 (z) must get the z: 3 value"
    );
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
    assert_eq!(
        fields[0].kind,
        HirExprKind::Integer(1),
        "paren form must match brace form: declared slot 0 (x)"
    );
    assert_eq!(
        fields[1].kind,
        HirExprKind::Integer(2),
        "paren form must match brace form: declared slot 1 (y)"
    );
    assert_eq!(
        fields[2].kind,
        HirExprKind::Integer(3),
        "paren form must match brace form: declared slot 2 (z)"
    );
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
    assert_eq!(
        fields[1].kind,
        HirExprKind::Nil,
        "y omitted -- must nil-fill, not shift z into slot 1"
    );
    assert_eq!(
        fields[2].kind,
        HirExprKind::Integer(30),
        "z provided, must stay in its own declared slot"
    );
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
    assert_eq!(
        fields.len(),
        3,
        "all 3 declared fields must be present even with zero provided args"
    );
    for (idx, field) in fields.iter().enumerate() {
        assert_eq!(
            field.kind,
            HirExprKind::Nil,
            "slot {idx} must nil-fill when nothing is provided"
        );
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

/// stage2 native enum-dispatch wall (2026-08-28): an `if val pl = optional:`
/// binding carries the POINTER (`T?`) type, so `match pl: case Variant(x)`
/// must still resolve the variant's payload field types through the pointee
/// enum. Pre-fix, the expected-type branch only unwrapped Pointer for `Some`,
/// so every other variant fell into the wildcard "_" search — a HashMap walk
/// returning the FIRST enum owning a same-named variant, per-process-random
/// when a decoy enum shares the name (`Tuple` has 3+ owners in the compiler
/// closure). That typed the binding ANY, downstream field access was
/// index-guessed against an unrelated struct, and the compiled stage2 binary
/// dispatched `match pat.kind` to `case _` (the `nested match pattern kind
/// not supported inside an enum payload` wall, plus the add-two-dead-externs
/// heisenbug).
#[test]
fn optional_enum_payload_binding_resolves_variant_fields_through_pointer() {
    use crate::hir::lower::lowerer::Lowerer;
    use crate::hir::{HirType, TypeId};

    let mut lowerer = Lowerer::new();
    // A decoy enum with the same bare variant name but a DIFFERENT payload
    // shape. Registered FIRST so a first-match walk that ignored the expected
    // type can plausibly land on it.
    let decoy = lowerer.module.types.register(HirType::Enum {
        name: "DecoyPayload".to_string(),
        variants: vec![
            ("Tuple".to_string(), Some(vec![TypeId::I64, TypeId::STRING])),
            ("Other".to_string(), None),
        ],
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: Default::default(),
    });
    let _ = decoy;
    let pat_array = lowerer.module.types.register(HirType::Array {
        element: TypeId::ANY,
        size: None,
    });
    let payload_enum = lowerer.module.types.register(HirType::Enum {
        name: "PPayload".to_string(),
        variants: vec![("Tuple".to_string(), Some(vec![pat_array]))],
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: Default::default(),
    });
    let optional_payload = lowerer.module.types.register(HirType::Pointer {
        kind: crate::hir::PointerKind::Shared,
        capability: simple_parser::ast::ReferenceCapability::Shared,
        inner: payload_enum,
    });

    // The subject is typed `PPayload?` (Pointer to the enum), exactly what an
    // `if val pl = payload:` unwrap binding carries. The variant is spelled
    // bare (`case Tuple(...)`), so enum_name is the parser's "_" placeholder.
    let fields = lowerer.get_enum_variant_field_types_with_hint("_", "Tuple", optional_payload);
    assert_eq!(
        fields,
        Some(vec![pat_array]),
        "payload field types must come from the POINTEE enum (PPayload), not \
         from a HashMap-order-dependent walk that can land on DecoyPayload"
    );
}

/// Genuine-ambiguity tie-break path in the wildcard `"_"` variant-owner
/// search: when TWO enums both own a variant of the same bare name AND their
/// payload shapes genuinely disagree, `get_enum_variant_field_types_with_hint`
/// cannot resolve the receiver's real owner from an ANY expected type alone.
/// It must not silently return whichever HashMap iteration produced first
/// (the original heisenbug); instead it must deterministically pick by
/// smallest owner name, so a wrong pick is at least stable and diagnosable.
/// This exercises the branch the accepted verify report flagged as untested
/// (`VERIFY_enum_dispatch.md` §2 / §3b): "No test covers the tie-break path".
#[test]
fn ambiguous_wildcard_variant_owner_picks_smallest_name_deterministically() {
    use crate::hir::lower::lowerer::Lowerer;
    use crate::hir::{HirType, TypeId};

    let mut lowerer = Lowerer::new();
    // Two owners of a same-named variant, genuinely different payloads, and
    // no Pointer/expected-type information to disambiguate (ANY receiver).
    let _zeta = lowerer.module.types.register(HirType::Enum {
        name: "ZetaKind".to_string(),
        variants: vec![("Shared".to_string(), Some(vec![TypeId::I64]))],
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: Default::default(),
    });
    let _alpha = lowerer.module.types.register(HirType::Enum {
        name: "AlphaKind".to_string(),
        variants: vec![("Shared".to_string(), Some(vec![TypeId::STRING, TypeId::BOOL]))],
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: Default::default(),
    });

    let fields = lowerer.get_enum_variant_field_types_with_hint("_", "Shared", TypeId::ANY);
    // "AlphaKind" < "ZetaKind" lexicographically -> deterministic pick must
    // be AlphaKind's payload, every run, regardless of registration order or
    // per-process HashMap RandomState.
    assert_eq!(
        fields,
        Some(vec![TypeId::STRING, TypeId::BOOL]),
        "on genuine disagreement the wildcard search must deterministically \
         pick the smallest-named owner (AlphaKind), not a random HashMap-order \
         first-match"
    );
}
