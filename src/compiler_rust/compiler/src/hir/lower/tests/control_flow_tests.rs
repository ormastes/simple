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
fn test_exists_check_uses_presence_predicate_without_nil_equality() {
    let module = parse_and_lower("fn present(value: i64?) -> bool:\n    return value.?\n").unwrap();
    let repr = format!("{:?}", module.functions[0].body);

    assert!(
        repr.contains("BuiltinCall") && repr.contains("rt_is_some"),
        "existence check did not use presence predicate: {repr}"
    );
    assert!(
        !repr.contains("NotEq") && !repr.contains("Nil"),
        "existence check retained generic nil equality: {repr}"
    );
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
fn test_optional_struct_pattern_binding_preserves_inner_type() {
    let module = parse_and_lower(
        "struct Mapping:\n    allocation_id: u64\n    owner_id: u64\n\nfn lookup() -> Mapping?:\n    nil\n\nfn owner() -> u64:\n    match lookup():\n        Some(mapping):\n            return mapping.owner_id\n        None:\n            return 0\n",
    )
    .unwrap();

    let owner = module
        .functions
        .iter()
        .find(|function| function.name == "owner")
        .unwrap();
    let mapping = owner.locals.iter().find(|local| local.name == "mapping").unwrap();
    assert!(matches!(
        module.types.get(mapping.ty),
        Some(HirType::Struct { name, .. }) if name == "Mapping"
    ));
    let owner_body = format!("{:?}", owner.body);
    assert!(
        owner_body.contains("rt_enum_payload"),
        "Some-binding must extract the materialized Option payload: {owner_body}"
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
    let HirStmt::For {
        pattern_local,
        iterable,
        ..
    } = &func.body[2]
    else {
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

/// A3 cranelift gap: positional class pattern `case ClassName(a, b, c)` must lower
/// with Bool(true) condition (not rt_enum_check_discriminant) and FieldAccess
/// bindings (not rt_enum_payload) so compiled/JIT mode matches correctly.
///
/// Regression for bug: positional_class_match_wide_destructure_2026-06-11.md
#[test]
fn test_positional_class_pattern_match_lowering() {
    // match statement using positional class pattern
    let source = "class Point:\n    x: i64\n    y: i64\n    z: i64\n\nfn run(p: Point) -> i64:\n    match p:\n        case Point(a, b, c):\n            return a\n        case _:\n            return 0\n";
    let module = parse_and_lower(source).unwrap();

    // Verify the Point type is a struct
    let point_tid = module.types.lookup("Point").expect("Point type not found");
    assert!(
        matches!(module.types.get(point_tid), Some(HirType::Struct { name, .. }) if name == "Point"),
        "Point should be a Struct type"
    );

    let func = &module.functions[0];

    // Find the first HirStmt::If in the body (the match arm).
    // There may be Let stmts before it (e.g. parameter copies).
    // Its condition must be Bool(true) — NOT a BuiltinCall to rt_enum_check_discriminant.
    let match_if = func
        .body
        .iter()
        .find(|s| matches!(s, HirStmt::If { .. }))
        .unwrap_or_else(|| panic!("expected a HirStmt::If in function body; body: {:?}", func.body));

    let HirStmt::If {
        condition, then_block, ..
    } = match_if
    else {
        unreachable!()
    };

    assert!(
        matches!(condition.kind, HirExprKind::Bool(true)),
        "positional class pattern condition must be Bool(true), not a discriminant check; got: {:?}",
        condition.kind
    );

    // The then_block must include FieldAccess bindings for a, b, c at indices 0, 1, 2.
    // FieldAccess maps field_index to byte_offset = i*8, which matches the flat struct layout
    // allocated by rt_alloc in the compiled path (fields at 0, 8, 16, …).
    let repr = format!("{:?}", then_block);
    assert!(
        repr.contains("FieldAccess"),
        "positional class pattern bindings must use FieldAccess; then_block repr: {repr}"
    );
    // Confirm rt_enum_payload is NOT used for the class pattern bindings
    assert!(
        !repr.contains("rt_enum_payload"),
        "positional class pattern must NOT use rt_enum_payload; then_block repr: {repr}"
    );
}

/// Enum variant positional patterns must still use rt_enum_check_discriminant
/// (regression guard: class-pattern fix must not affect enum matching).
#[test]
fn test_enum_variant_pattern_condition_still_uses_discriminant() {
    let source = "enum Color:\n    Red\n    Green\n    Blue\n\nfn is_red(c: Color) -> i64:\n    match c:\n        case Color.Red:\n            return 1\n        case _:\n            return 0\n";
    let module = parse_and_lower(source).unwrap();

    let func = &module.functions[0];

    // Find the first HirStmt::If whose condition uses rt_enum_check_discriminant.
    let match_if = func
        .body
        .iter()
        .find(|s| matches!(s, HirStmt::If { .. }))
        .unwrap_or_else(|| panic!("expected a HirStmt::If in function body"));

    let HirStmt::If { condition, .. } = match_if else {
        unreachable!()
    };

    let repr = format!("{:?}", condition.kind);
    assert!(
        repr.contains("rt_enum_check_discriminant") || repr.contains("rt_is_none") || repr.contains("rt_is_some"),
        "enum variant pattern condition should use rt_enum_check_discriminant; got: {repr}"
    );
}

#[test]
fn test_multi_field_enum_payload_keeps_array_type() {
    let source = "enum Payload:\n    Item(text, i64, text)\n\nfn third(value: Payload) -> text:\n    match value:\n        case Payload.Item(_, _, result):\n            return result\n        case _:\n            return \"\"\n";
    let module = parse_and_lower(source).unwrap();
    let repr = format!("{:?}", module.functions[0].body);

    assert!(
        repr.contains("rt_enum_payload"),
        "missing enum payload extraction: {repr}"
    );
    assert!(repr.contains("Index"), "missing payload field index: {repr}");

    let array_type_is_present = module
        .types
        .iter()
        .any(|(_, ty)| matches!(ty, HirType::Array { element, size: Some(3) } if *element == TypeId::ANY));
    assert!(
        array_type_is_present,
        "multi-field payload receiver was not typed as [any; 3]"
    );

    let mir = crate::mir::lower_to_mir(&module).expect("MIR lowering should succeed");
    let mir_repr = format!("{mir:?}");
    assert!(
        mir_repr.contains("rt_array_get"),
        "payload extraction did not use rt_array_get: {mir_repr}"
    );
    assert!(
        !mir_repr.contains("rt_index_get"),
        "payload extraction retained generic rt_index_get: {mir_repr}"
    );
}

#[test]
fn test_subject_enum_const_variant_beats_unrelated_const_struct() {
    let source = "class Const:\n    value: i64\n\nenum Inst:\n    Const(i64, i64, i64)\n    Other\n\nfn destination(inst: Inst) -> i64:\n    val result = match inst:\n        case Const(dest, _, _):\n            dest\n        case _:\n            -1\n    return result\n";
    let module = parse_and_lower(source).unwrap();
    let repr = format!("{:?}", module.functions[0].body);

    assert!(matches!(
        module.types.lookup("Const").and_then(|tid| module.types.get(tid)),
        Some(HirType::Struct { .. })
    ));
    assert!(
        repr.contains("rt_enum_check_discriminant"),
        "subject-owned Const variant must remain refutable despite unrelated Const struct: {repr}"
    );
    assert!(
        repr.contains("rt_enum_payload"),
        "subject-owned Const variant must extract its payload fields: {repr}"
    );
}

#[test]
fn test_if_let_multi_field_enum_payload_uses_array_get() {
    let source = "enum Payload:\n    Item(text, i64, text)\n\nfn third(value: Payload) -> text:\n    if val Payload.Item(_, _, result) = value:\n        return result\n    return \"\"\n";
    let module = parse_and_lower(source).unwrap();
    let mir = crate::mir::lower_to_mir(&module).expect("MIR lowering should succeed");
    let mir_repr = format!("{mir:?}");

    assert!(
        mir_repr.contains("rt_array_get"),
        "if-let payload did not use rt_array_get: {mir_repr}"
    );
    assert!(
        !mir_repr.contains("rt_index_get"),
        "if-let payload retained generic rt_index_get: {mir_repr}"
    );
}

#[test]
fn test_standalone_match_subject_enum_const_variant_beats_unrelated_const_struct() {
    let source = "class Const:\n    value: i64\n\nenum Inst:\n    Const(i64, i64, i64)\n    Other\n\nfn destination(inst: Inst) -> i64:\n    match inst:\n        case Const(dest, _, _):\n            return dest\n        case _:\n            return -1\n";
    let module = parse_and_lower(source).unwrap();
    let repr = format!("{:?}", module.functions[0].body);

    assert!(matches!(
        module.types.lookup("Const").and_then(|tid| module.types.get(tid)),
        Some(HirType::Struct { .. })
    ));
    assert!(
        repr.contains("rt_enum_check_discriminant"),
        "standalone match must discriminate its subject-owned Const variant: {repr}"
    );
    assert!(
        repr.contains("rt_enum_payload"),
        "standalone match must extract its subject-owned Const payload: {repr}"
    );
}

#[test]
fn test_regular_if_patterned_elif_binds_local() {
    let source = "fn unwrap_after_regular(value: i64?) -> i64:\n    if false:\n        return 0\n    elif val unwrapped = value:\n        return unwrapped\n    return -1\n";
    let module = parse_and_lower(source).unwrap();
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "unwrap_after_regular")
        .unwrap();
    let hir_repr = format!("{:?}", function.body);

    assert!(
        function.locals.iter().any(|local| local.name == "unwrapped"),
        "{hir_repr}"
    );
    assert!(!hir_repr.contains("Global(\"unwrapped\")"), "{hir_repr}");

    let mir = crate::mir::lower_to_mir(&module).expect("MIR lowering should succeed");
    let mir_repr = format!("{mir:?}");
    assert!(!mir_repr.contains("global_name: \"unwrapped\""), "{mir_repr}");
}

#[test]
fn test_implicit_self_inside_if_let_cast_binds_local() {
    let source = "class Buffer:\n    inner: i64\n\n    fn read_cast() -> i64:\n        if val value = self.inner as i64:\n            return value\n        return 0\n";
    let module = parse_and_lower(source).unwrap();
    let function = module.functions.iter().find(|f| f.name.ends_with("read_cast")).unwrap();
    let hir_repr = format!("{:?}", function.body);

    assert!(function.params.iter().any(|param| param.name == "self"), "{hir_repr}");
    assert!(!hir_repr.contains("Global(\"self\")"), "{hir_repr}");

    let mir = crate::mir::lower_to_mir(&module).expect("MIR lowering should succeed");
    let mir_repr = format!("{mir:?}");
    assert!(!mir_repr.contains("global_name: \"self\""), "{mir_repr}");
}
