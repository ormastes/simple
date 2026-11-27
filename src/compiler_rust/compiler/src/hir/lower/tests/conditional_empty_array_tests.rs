use super::parse_and_lower;
use crate::hir::types::{HirExprKind, HirStmt, HirType, TypeId};

#[test]
fn conditional_empty_array_preserves_symbol_keys_in_both_orders() {
    for expression in ["if empty: [] else: symbols.keys()", "if empty: symbols.keys() else: []"] {
        let source = format!("struct SymbolId:\n    id: i64\nfn probe(symbols: Dict<SymbolId, i64>, empty: bool) -> i64:\n    val keys = {expression}\n    for key in keys:\n        val observed = key.id\n    0\n");
        let module = parse_and_lower(&source).unwrap();
        let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
        let keys = function.locals.iter().find(|l| l.name == "keys").unwrap();
        let Some(HirType::Array { element, size }) = module.types.get(keys.ty) else { panic!("keys is not an array") };
        assert!(matches!(module.types.get(*element), Some(HirType::Struct { name, .. }) if name == "SymbolId"), "{expression}: {:?}", module.types.get(*element));
        assert_eq!(*size, None);
        let key = function.locals.iter().find(|l| l.name == "key").unwrap();
        assert_eq!(key.ty, *element);
        let HirStmt::Let { value: Some(value), .. } = &function.body[0] else { panic!("expected keys initializer") };
        let HirExprKind::If { then_branch, else_branch: Some(other), .. } = &value.kind else { panic!("expected conditional") };
        for branch in [then_branch, other] {
            let Some(HirType::Array { element: branch_element, .. }) = module.types.get(branch.ty) else { panic!("expected array branch") };
            assert_eq!(branch_element, element);
        }
    }
}

#[test]
fn conditional_empty_array_does_not_retype_populated_or_unrelated_aggregates() {
    for (expression, expected) in [
        ("if flag: [] else: (1, 2)", TypeId::I32),
        ("if flag: [] else: []", TypeId::I32),
        ("if flag: [\"typed\"; 0] else: [1]", TypeId::STRING),
        ("if flag: [] else: [\"typed\"; 0]", TypeId::STRING),
    ] {
        let source = format!("fn probe(flag: bool, words: [text]) -> i64:\n    val items = {expression}\n    0\n");
        let module = parse_and_lower(&source).unwrap();
        let items = module.functions[0].locals.iter().find(|l| l.name == "items").unwrap();
        assert!(matches!(module.types.get(items.ty), Some(HirType::Array { element, .. }) if *element == expected), "{expression}");
    }
}

#[test]
fn multiline_if_elif_empty_array_never_narrows_struct_or_any_elements_to_i32() {
    // Repro for seed_native_build_lint_entry_hir_i32_code_field_2026-11-20:
    // `entry_and_fixes.spl` wrote a multiline `if not run_opt_me:\n    []\nelif ...`
    // whose `then_branch` parsed as `Expr::DoBlock([Expression(Array([]))])` and
    // whose `elif` arm could resolve to either `[OptionMeCallWarning]` or `ANY`
    // across modules. Before the fix, `[]` kept its `[i32]` default and `warning.code`
    // failed with `Cannot infer field type: struct 'i32' field 'code'`.
    let typed_source = concat!(
        "struct OptionMeCallWarning:\n",
        "    code: text\n",
        "fn make_warnings() -> [OptionMeCallWarning]:\n",
        "    []\n",
        "fn probe_typed(run_opt_me: bool, cached_ok: bool, cached: [OptionMeCallWarning]) -> text:\n",
        "    val option_me_warnings = if not run_opt_me:\n",
        "        []\n",
        "    elif cached_ok:\n",
        "        cached\n",
        "    else:\n",
        "        make_warnings()\n",
        "    for warning in option_me_warnings:\n",
        "        return warning.code\n",
        "    \"\"\n",
    );
    let typed_mod = parse_and_lower(typed_source).expect("multiline typed if/elif empty array must lower");
    let typed_fn = typed_mod.functions.iter().find(|f| f.name == "probe_typed").unwrap();
    let warning_local = typed_fn.locals.iter().find(|l| l.name == "warning").unwrap();
    assert!(
        matches!(typed_mod.types.get(warning_local.ty), Some(HirType::Struct { name, .. }) if name == "OptionMeCallWarning"),
        "expected OptionMeCallWarning element, got {:?}",
        typed_mod.types.get(warning_local.ty)
    );

    // Dynamic `ANY` sibling in `elif` (cross-module field whose type erased to ANY).
    let dynamic_source = concat!(
        "struct OptionMeCallWarning:\n",
        "    code: text\n",
        "extern fn dynamic_cached() -> Any\n",
        "fn make_warnings() -> [OptionMeCallWarning]:\n",
        "    []\n",
        "fn probe_dynamic(run_opt_me: bool, cached_ok: bool) -> text:\n",
        "    val option_me_warnings = if not run_opt_me:\n",
        "        []\n",
        "    elif cached_ok:\n",
        "        dynamic_cached()\n",
        "    else:\n",
        "        make_warnings()\n",
        "    for warning in option_me_warnings:\n",
        "        return warning.code\n",
        "    \"\"\n",
    );
    let dyn_mod = parse_and_lower(dynamic_source).expect("multiline ANY-sibling if/elif empty array must lower");
    let dyn_fn = dyn_mod.functions.iter().find(|f| f.name == "probe_dynamic").unwrap();
    let dyn_warning = dyn_fn.locals.iter().find(|l| l.name == "warning").unwrap();
    assert_ne!(dyn_warning.ty, TypeId::I32, "loop element must never degrade to i32");
}

#[test]
fn multi_branch_and_nested_if_empty_arrays_propagate_sibling_element_to_all_leaves() {
    // Shape 1: `if c1: bytes elif c2: [] else: []` where `bytes: [u8]`.
    // Both trailing `[]` leaves and the inner `If` must retype to `u8` so MIR
    // emits `rt_byte_array_new` instead of generic `[i32; 0]` `rt_array_new`.
    let trailing_source = concat!(
        "fn probe_bytes(c1: bool, c2: bool, bytes: [u8]) -> [u8]:\n",
        "    val out = if c1: bytes elif c2: [] else: []\n",
        "    out\n",
    );
    let trailing_mod = parse_and_lower(trailing_source).expect("trailing elif/else empty u8 arrays must lower");
    let trailing_fn = trailing_mod.functions.iter().find(|f| f.name == "probe_bytes").unwrap();
    let out_local = trailing_fn.locals.iter().find(|l| l.name == "out").unwrap();
    assert!(
        matches!(trailing_mod.types.get(out_local.ty), Some(HirType::Array { element, size: None }) if *element == TypeId::U8),
        "expected [u8] local, got {:?}",
        trailing_mod.types.get(out_local.ty)
    );
    let HirStmt::Let { value: Some(outer_if), .. } = &trailing_fn.body[0] else {
        panic!("expected out initializer");
    };
    let HirExprKind::If {
        else_branch: Some(inner_if),
        ..
    } = &outer_if.kind
    else {
        panic!("expected outer If");
    };
    assert!(
        matches!(trailing_mod.types.get(inner_if.ty), Some(HirType::Array { element, .. }) if *element == TypeId::U8),
        "expected inner If to retype to u8 array, got {:?}",
        trailing_mod.types.get(inner_if.ty)
    );
    let HirExprKind::If {
        then_branch: inner_then,
        else_branch: Some(inner_else),
        ..
    } = &inner_if.kind
    else {
        panic!("expected inner If");
    };
    for leaf in [inner_then, inner_else] {
        assert!(
            matches!(
                trailing_mod.types.get(leaf.ty),
                Some(HirType::Array {
                    element,
                    size: Some(0)
                }) if *element == TypeId::U8
            ),
            "expected [u8; 0] leaf, got {:?}",
            trailing_mod.types.get(leaf.ty)
        );
    }

    // Shape 2: `if c1: (if c2: [] else: []) else: make_warnings()`.
    let leading_source = concat!(
        "struct OptionMeCallWarning:\n",
        "    code: text\n",
        "fn make_warnings() -> [OptionMeCallWarning]:\n",
        "    []\n",
        "fn probe_leading(c1: bool, c2: bool) -> text:\n",
        "    val warnings = if c1: (if c2: [] else: []) else: make_warnings()\n",
        "    for warning in warnings:\n",
        "        return warning.code\n",
        "    \"\"\n",
    );
    let leading_mod = parse_and_lower(leading_source).expect("nested leading empty-array If must lower");
    let leading_fn = leading_mod.functions.iter().find(|f| f.name == "probe_leading").unwrap();
    let warning_local = leading_fn.locals.iter().find(|l| l.name == "warning").unwrap();
    assert!(
        matches!(leading_mod.types.get(warning_local.ty), Some(HirType::Struct { name, .. }) if name == "OptionMeCallWarning"),
        "expected OptionMeCallWarning loop element, got {:?}",
        leading_mod.types.get(warning_local.ty)
    );
}

const TAG_CLASSES: &str = concat!(
    "class Tag:\n    n: text\n    fn label() -> text?:\n        Some(self.n)\n    fn entries() -> Dict<text, Tag>?:\n        None\n",
    "class Other:\n    n: text\n    fn label() -> text?:\n        Some(self.n)\n",
    "fn other_label(o: Other) -> text:\n    o.label() ?? \"\"\n",
);

fn local_ty(module: &crate::hir::HirModule, func: &str, local: &str) -> Option<HirType> {
    let function = module.functions.iter().find(|f| f.name == func).unwrap();
    let l = function.locals.iter().find(|l| l.name == local).unwrap();
    module.types.get(l.ty).cloned()
}

#[test]
fn nested_tail_match_arm_keeps_payload_type_for_dict_index_receiver() {
    // A `match` that is the sole body of an outer match arm is a tail match
    // STATEMENT; it used to type the arm block NIL/ANY, so `files` lost its
    // `Dict<text, Tag>` type and `files[k].label()` reached codegen as a bare
    // method call with 2+ candidates (CODEGEN-AMBIGUOUS-METHOD).
    let source = format!(
        "{TAG_CLASSES}fn pick(outer: Tag?, key: text) -> text:\n    val files = match outer:\n        case Some(a):\n            match a.entries():\n                case Some(entries): entries\n                case None: return \"x\"\n        case None: return \"y\"\n    files[key].label() ?? \"\"\n"
    );
    let module = parse_and_lower(&source).unwrap();
    let Some(HirType::Dict { key, value }) = local_ty(&module, "pick", "files") else {
        panic!("files must keep its Dict type, got {:?}", local_ty(&module, "pick", "files"));
    };
    assert_eq!(key, TypeId::STRING);
    assert!(matches!(module.types.get(value), Some(HirType::Struct { name, .. }) if name == "Tag"), "{:?}", module.types.get(value));
}

#[test]
fn nested_match_empty_dict_arm_does_not_beat_concrete_sibling_dict() {
    // `{}` default type is not evidence: the concrete outer sibling must win.
    let source = format!(
        "{TAG_CLASSES}enum K:\n    A\n    B\nfn pick(d: Dict<text, Tag>, a: i64?, k: K) -> text:\n    val files = match a:\n        case Some(x):\n            match k:\n                case K.A: {{}}\n                case K.B: d\n        case None: d\n    files[\"k\"].label() ?? \"\"\n"
    );
    let module = parse_and_lower(&source).unwrap();
    let Some(HirType::Dict { key, value }) = local_ty(&module, "pick", "files") else {
        panic!("files must be the sibling Dict, got {:?}", local_ty(&module, "pick", "files"));
    };
    assert_eq!(key, TypeId::STRING);
    assert!(matches!(module.types.get(value), Some(HirType::Struct { name, .. }) if name == "Tag"));
}

#[test]
fn match_empty_array_arm_does_not_beat_concrete_sibling_array() {
    // Nested, nested-if and flat shapes: `[]` (default [i32]) must not win the
    // join over a `[f64]` sibling (silent wrong value: 1.75 vs 1006847761.25).
    for body in [
        "    val r = match a:\n        case Some(x):\n            match k:\n                case K.A: []\n                case K.B: return -1.0\n        case None: xs\n",
        "    val r = match a:\n        case Some(x):\n            if c:\n                []\n            else:\n                return -1.0\n        case None: xs\n",
        "    val r = match k:\n        case K.A: []\n        case K.B: xs\n",
    ] {
        let source = format!(
            "enum K:\n    A\n    B\nfn h(xs: [f64], a: i64?, k: K, c: bool) -> f64:\n{body}    if r.len() > 0: r[0] + 0.25 else: -2.0\n"
        );
        let module = parse_and_lower(&source).unwrap();
        let Some(HirType::Array { element, .. }) = local_ty(&module, "h", "r") else {
            panic!("r must be an array for {body}");
        };
        assert_eq!(element, TypeId::F64, "{body}");
    }
}

#[test]
fn if_join_weak_empty_match_arm_does_not_beat_concrete_sibling() {
    // The IF join must apply the same weak-empty rule as the match join when a
    // branch is a (now typed) tail match whose value arms are only `[]`/`{}`.
    let k = "enum K:\n    A\n    B\n    C\n";
    for (body, want_array) in [
        ("    val r = if c:\n        match k:\n            case K.A: []\n            case K.B: return -7.0\n            case K.C: []\n    else:\n        xs\n", true),
        ("    val r = if n == 0:\n        match k:\n            case K.A: []\n            case K.B: return -7.0\n            case K.C: []\n    elif n == 1:\n        []\n    else:\n        xs\n", true),
        ("    val r = if c:\n        []\n    else:\n        xs\n", true),
    ] {
        let source = format!("{k}fn h(xs: [f64], c: bool, n: i64, k: K) -> f64:\n{body}    if r.len() > 0: r[0] + 0.25 else: -2.0\n");
        let module = parse_and_lower(&source).unwrap();
        let Some(HirType::Array { element, .. }) = local_ty(&module, "h", "r") else { panic!("r must be an array for {body}") };
        assert_eq!(element, TypeId::F64, "{body}");
        assert!(want_array);
    }
}

#[test]
fn if_join_weak_empty_dict_match_arm_does_not_beat_concrete_sibling_dict() {
    let source = format!(
        "{TAG_CLASSES}enum K:\n    A\n    B\n    C\nfn pick(d: Dict<text, Tag>, c: bool, k: K) -> text:\n    val files = if c:\n        match k:\n            case K.A: {{}}\n            case K.B: return \"r\"\n            case K.C: {{}}\n    else:\n        d\n    files[\"k\"].label() ?? \"\"\n"
    );
    let module = parse_and_lower(&source).unwrap();
    let Some(HirType::Dict { key, value }) = local_ty(&module, "pick", "files") else {
        panic!("files must be the sibling Dict, got {:?}", local_ty(&module, "pick", "files"));
    };
    assert_eq!(key, TypeId::STRING);
    assert!(matches!(module.types.get(value), Some(HirType::Struct { name, .. }) if name == "Tag"));
}

#[test]
fn weak_empty_rule_ignores_ill_kinded_and_explicit_repeat_siblings() {
    // `[]` vs a Dict sibling is ill-kinded: a type error in safe code (see
    // `disagreeing_value_arms_are_a_type_error_in_safe_code`); inside `unsafe`
    // the join keeps the `[]` side rather than adopt the Dict type.
    let k = "enum K:\n    A\n    B\n";
    let source = format!("{k}fn k3(d: Dict<text, i64>, kk: K) -> i64:\n    unsafe:\n        val r = match kk:\n            case K.A: []\n            case _: d\n    0\n");
    let module = parse_and_lower(&source).unwrap();
    assert!(matches!(local_ty(&module, "k3", "r"), Some(HirType::Array { .. })), "{:?}", local_ty(&module, "k3", "r"));

    // `[0; 0]` is an explicit typed repeat (lowers to an empty HIR array): it
    // keeps its own [i64] type in match arms, if/else and indented do-blocks.
    for body in [
        "    var r = match kk:\n        case K.A: [0; 0]\n        case _: xs\n",
        "    var r = if c:\n        [0; 0]\n    else:\n        xs\n",
        "    var r = if c: [0; 0] else: xs\n",
    ] {
        let source = format!("{k}fn rr(xs: [f64], kk: K, c: bool) -> i64:\n{body}    0\n");
        let module = parse_and_lower(&source).unwrap();
        let Some(HirType::Array { element, .. }) = local_ty(&module, "rr", "r") else { panic!("r must be an array for {body}") };
        assert_eq!(element, TypeId::I64, "{body}");
    }
}

fn local_type<'a>(module: &'a crate::hir::HirModule, name: &str) -> &'a HirType {
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let local = function.locals.iter().find(|l| l.name == name).unwrap();
    module.types.get(local.ty).unwrap()
}

fn option_payload<'a>(module: &'a crate::hir::HirModule, ty: &'a HirType) -> &'a HirType {
    let HirType::Enum { name, variants, .. } = ty else { panic!("expected Option enum, got {ty:?}") };
    assert_eq!(name, "Option");
    let (_, Some(payload)) = variants.iter().find(|(v, _)| v == "Some").unwrap() else { panic!("Some has no payload") };
    module.types.get(payload[0]).unwrap()
}

#[test]
fn option_wrapped_empty_array_defers_to_concrete_sibling_in_if_and_match() {
    let if_forms = ["if c: Some([]) else: Some(xs)", "if c: Some(xs) else: Some([])"];
    let match_forms = [
        "match k:\n        case 0: Some([])\n        case _: Some(xs)",
        "match k:\n        case 0: Some(xs)\n        case _: Some([])",
    ];
    for expression in if_forms.iter().chain(match_forms.iter()) {
        let source = format!(
            "fn probe(xs: [f64], c: bool, k: i64) -> f64:\n    val r = {expression}\n    match r:\n        case Some(v): v[0]\n        case None: 0.0\n"
        );
        let module = parse_and_lower(&source).unwrap();
        let r_ty = local_type(&module, "r");
        let HirType::Array { element, .. } = option_payload(&module, r_ty) else { panic!("{expression}: payload is not an array") };
        assert_eq!(*element, TypeId::F64, "{expression}: join must keep the concrete sibling's element type");
        let HirType::Array { element, .. } = local_type(&module, "v") else { panic!("{expression}: v is not an array") };
        assert_eq!(*element, TypeId::F64, "{expression}");
    }
}

#[test]
fn option_wrapped_arrays_do_not_defer_when_not_weak_or_not_collections() {
    // `Some([x; 0])` is an explicit repeat (never weak); `Some([])` vs `Some([])` and
    // `Some([])` vs `Some(5)` keep the first arm's own type.
    for expression in ["if c: Some([\"t\"; 0]) else: Some(xs)", "if c: Some([]) else: Some(5)"] {
        let source = format!(
            "fn probe(xs: [f64], c: bool) -> i64:\n    val r = {expression}\n    0\n"
        );
        let module = parse_and_lower(&source).unwrap();
        let r_ty = local_type(&module, "r");
        if matches!(r_ty, HirType::Any) {
            continue; // untyped Some(..) stays erased: nothing adopted from the sibling
        }
        let HirType::Array { element, .. } = option_payload(&module, r_ty) else { panic!("{expression}: payload is not an array") };
        assert_ne!(*element, TypeId::F64, "{expression}: must not adopt the sibling element type");
    }
}

fn assert_not_i32_array_option(module: &crate::hir::HirModule, ty: &HirType, what: &str) {
    if let HirType::Enum { name, .. } = ty {
        if name == "Option" {
            let HirType::Array { element, .. } = option_payload(module, ty) else { return };
            assert_ne!(*element, TypeId::I32, "{what}: bare `Some([])` must not become authoritative Option<[i32]>");
        }
    }
    if let HirType::Array { element, .. } = ty {
        assert_ne!(*element, TypeId::I32, "{what}: payload must not be the i32 default");
    }
}

#[test]
fn some_empty_array_stays_weak_when_later_replaced_or_filled() {
    // a02: `var o = Some([]); o = Some([1.5, 2.5])`, a18: fill through the bound payload,
    // c04: `if c: Some([]) else: None` then push.
    for (source, local) in [
        ("fn probe() -> f64:\n    var o = Some([])\n    o = Some([1.5, 2.5])\n    match o:\n        case Some(v): v[0] + 0.25\n        case None: 0.0\n", "o"),
        ("fn probe() -> f64:\n    var o = Some([])\n    match o:\n        case Some(v):\n            var w = v\n            w.push(2.5)\n            w[0]\n        case None: 0.0\n", "o"),
        ("fn probe() -> f64:\n    var o = Some([])\n    match o:\n        case Some(v):\n            var w = v\n            w.push(2.5)\n            w[0]\n        case None: 0.0\n", "v"),
        ("fn probe(c: bool) -> f64:\n    val r = if c: Some([]) else: None\n    match r:\n        case Some(v):\n            var w = v\n            w.push(1.5)\n            w[0]\n        case None: 0.0\n", "r"),
    ] {
        let module = parse_and_lower(source).unwrap();
        let ty = local_type(&module, local);
        assert_not_i32_array_option(&module, ty, local);
    }
}

#[test]
fn option_wrapped_empty_dict_defers_and_option_never_adopts_result() {
    let source = "fn probe(c: bool, base: Dict<text, f64>) -> f64:\n    val r = if c: Some({}) else: Some(base)\n    match r:\n        case Some(v): v[\"k\"]\n        case None: 0.0\n";
    let module = parse_and_lower(source).unwrap();
    let ty = local_type(&module, "r");
    let payload = option_payload(&module, ty);
    assert!(matches!(payload, HirType::Dict { .. }), "dict join must follow the concrete sibling: {payload:?}");

    let source = "fn probe(c: bool, xs: [f64]) -> i64:\n    val r = if c: Some([]) else: Ok(xs)\n    0\n";
    let module = parse_and_lower(source).unwrap();
    let ty = local_type(&module, "r");
    assert!(!matches!(ty, HirType::Enum { name, .. } if name == "Result"), "Some([]) must not adopt a Result type: {ty:?}");
}

#[test]
fn some_array_literal_payload_stays_erased_so_reassignment_and_mixed_pushes_stay_correct() {
    // b03: `Some([0])` later reassigned `Some([1.5, 2.5])`; b05: heterogeneous `Some([..])` pushes.
    for source in [
        "fn probe() -> f64:\n    var c2 = Some([0])\n    c2 = Some([1.5, 2.5])\n    0.0\n",
        "fn probe() -> f64:\n    val a = Some([1.5, 2.5])\n    0.0\n",
    ] {
        let module = parse_and_lower(source).unwrap();
        let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
        for local in function.locals.iter().filter(|l| l.name == "c2" || l.name == "a") {
            assert!(!matches!(module.types.get(local.ty), Some(HirType::Enum { .. })), "literal payload must not become authoritative Option<T>");
        }
    }
}

#[test]
fn option_wrapped_empty_literal_never_adopts_sibling_of_other_collection_kind() {
    // d10 k1/k2: an erased `Some([])` vs `Some(<dict>)` (and `Some({})` vs `Some(<array>)`)
    // must keep the first arm's type instead of adopting the other kind's Option.
    for (empty, base, bad_dict) in [("[]", "base", true), ("{}", "xs", false)] {
        let source = format!(
            "fn probe(c: bool, xs: [f64], base: Dict<text, f64>) -> i64:\n    val r = if c: Some({empty}) else: Some({base})\n    0\n"
        );
        let module = parse_and_lower(&source).unwrap();
        let ty = local_type(&module, "r");
        if let HirType::Enum { name, .. } = ty {
            if name == "Option" {
                let payload = option_payload(&module, ty);
                let is_dict = matches!(payload, HirType::Dict { .. });
                let is_array = matches!(payload, HirType::Array { .. });
                assert!(!(bad_dict && is_dict) && !(!bad_dict && is_array), "{empty} vs {base}: adopted the other kind: {payload:?}");
            }
        }
    }
}

// (C) disagreeing siblings: the first concrete arm's type used to win and the
// sibling arm was read through it as garbage. Safe code now gets a type error
// naming both arm types; int vs float is the one typed join (int -> float).
fn join_error(source: &str) -> String {
    match parse_and_lower(source) {
        Ok(_) => panic!("must not lower:\n{source}"),
        Err(e) => e.to_string(),
    }
}

#[test]
fn disagreeing_value_arms_are_a_type_error_in_safe_code() {
    for (expression, then_ty, else_ty) in [
        ("if c: 1 else: \"a\"", "`i64`", "`text`"),
        ("if c: {} else: 5", "`Dict`", "`i64`"),
        ("if c: [] else: \"txt\"", "`[", "`text`"),
        ("if c: [] else: d", "`[", "`Dict<text, i64>`"),
        ("if c: true else: 0", "`bool`", "`i64`"),
        ("if c: xs else: ys", "`[f64]`", "`[i64]`"),
        ("if c: [1] else: names", "`[i64]`", "`[text]`"),
    ] {
        let source = format!(
            "fn probe(c: bool, xs: [f64], ys: [i64], names: [text], d: Dict<text, i64>) -> i64:\n    val r = {expression}\n    0\n"
        );
        let msg = join_error(&source);
        assert!(msg.contains(crate::hir::LOWERING_TYPE_ERROR_TAG), "{expression}: {msg}");
        assert!(msg.contains("value arms disagree in `probe` (fn at line 1)"), "{expression}: {msg}");
        assert!(msg.contains(&format!("the then-arm is {then_ty}")), "{expression}: {msg}");
        assert!(msg.contains(&format!("the else-arm is {else_ty}")), "{expression}: {msg}");
    }
}

#[test]
fn disagreeing_match_arms_name_both_types_and_arm_lines() {
    let k = "enum K:\n    A\n    B\n    C\n";
    // probe n1 d1 / d2: `[]`, `[f64]`, `[i64]` in both orders.
    for (b, c, first, second) in [("xs", "ys", "`[f64]`", "`[i64]`"), ("ys", "xs", "`[i64]`", "`[f64]`")] {
        let source = format!(
            "{k}fn d(xs: [f64], ys: [i64], kk: K) -> i64:\n    val r = match kk:\n        case K.A: []\n        case K.B: {b}\n        case K.C: {c}\n    r.len()\n"
        );
        let msg = join_error(&source);
        assert!(msg.contains(&format!("the arm at line 8 is {first} but the arm(s) from line 9 is {second}")), "{msg}");
    }
    // probe p_kind k6: `{}` vs `5`.
    let msg = join_error(&format!("{k}fn k6(kk: K) -> i64:\n    val r = match kk:\n        case K.A: {{}}\n        case _: 5\n    0\n"));
    assert!(msg.contains("value arms disagree in `k6`") && msg.contains("`i64`"), "{msg}");
    // `if val` expression form.
    let msg = join_error("fn o(x: i64?) -> i64:\n    val r = if val Some(v) = x: v else: \"none\"\n    0\n");
    assert!(msg.contains("the then-arm is `i64` but the else-arm is `text`"), "{msg}");
}

#[test]
fn int_and_float_arms_join_to_float_by_converting_the_int_arm() {
    for (expression, int_is_then) in [("if c: 1.5 else: 2", false), ("if c: n else: x", true)] {
        let source = format!("fn probe(c: bool, n: i64, x: f64) -> f64:\n    val r = {expression}\n    r\n");
        let module = parse_and_lower(&source).unwrap();
        assert_eq!(local_ty(&module, "probe", "r"), Some(HirType::Float { bits: 64 }), "{expression}");
        let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
        let HirStmt::Let { value: Some(value), .. } = &function.body[0] else { panic!("expected initializer") };
        let HirExprKind::If { then_branch, else_branch: Some(other), .. } = &value.kind else { panic!("expected conditional") };
        let (int_arm, float_arm) = if int_is_then { (then_branch, other) } else { (other, then_branch) };
        assert!(matches!(&int_arm.kind, HirExprKind::Cast { target, .. } if *target == TypeId::F64), "{expression}");
        assert!(!matches!(&float_arm.kind, HirExprKind::Cast { .. }), "{expression}");
    }
    let source = "fn probe(k: i64) -> f64:\n    val r = match k:\n        case 0: 1\n        case 1: 2.5\n        case _: 3\n    r\n";
    let module = parse_and_lower(source).unwrap();
    assert_eq!(local_ty(&module, "probe", "r"), Some(HirType::Float { bits: 64 }));
}

#[test]
fn value_join_rule_leaves_agreeing_bottom_weak_unsafe_and_statement_forms_alone() {
    let k = "enum K:\n    A\n    B\nfn p(x: i64) -> i64:\n    x\nfn q(x: i64) -> text:\n    \"q\"\n";
    for body in [
        // agreeing / width-only / weak-empty / bottom arms
        "    val r = if c: xs else: xs\n",
        "    val r = if c: 1 else: 2\n",
        "    val r = if c: [] else: xs\n",
        "    val r = match kk:\n        case K.A: []\n        case _: xs\n",
        "    val r = if c: 1 else: nil\n",
        "    val r = match kk:\n        case K.A: return 7\n        case _: \"t\"\n",
        // an arm that leaves through `continue` yields no value
        "    for i in [1, 2]:
        val t = match kk:
            case K.A: \"t\"
            case _:
                xs.len()
                continue
",
        // a statement-form match discards its value: nothing is joined
        "    match kk:\n        case K.A: p(1)\n        case K.B: q(2)\n",
        // `unsafe` keeps the untyped join
        "    unsafe:\n        val r = if c: 1 else: \"a\"\n",
        "    unsafe:\n        val r = match kk:\n            case K.A: xs\n            case _: [1]\n",
    ] {
        let source = format!("{k}fn probe(c: bool, kk: K, xs: [f64]) -> i64:\n{body}    0\n");
        parse_and_lower(&source).unwrap_or_else(|e| panic!("must lower:\n{body}{e}"));
    }
}

#[test]
fn script_entry_functions_keep_the_untyped_join_and_compiled_entries_do_not() {
    let source = "fn probe(c: bool) -> i64:\n    val r = if c: 1 else: \"a\"\n    0\n";
    crate::hir::set_entry_script_mode(true);
    let script = parse_and_lower(source);
    crate::hir::set_entry_script_mode(false);
    script.expect("a script entry function runs on the interpreter and is not checked");
    assert!(join_error(source).contains("value arms disagree"));
}

#[test]
fn promoted_float_join_never_reaches_an_int_slot() {
    let p = "struct P:\n    n: i64\n";
    for (body, slot) in [
        ("    val r: i64 = if c: 1 else: 2.5\n", "binding `r`"),
        ("    val r: i64 = match n:\n        case 0: n\n        case 1: n * 2\n        case _: 0.0\n", "binding `r`"),
        ("    var r = 0\n    r = if c: 1 else: 2.5\n", "the assignment target"),
        ("    val p = P(n: if c: n else: 2.5)\n", "field `P.n`"),
        ("    val r = if c: n else: 2.5\n    val xs = [10, 20, 30]\n    val e = xs[r]\n", "the index"),
    ] {
        let msg = join_error(&format!("{p}fn probe(c: bool, n: i64) -> i64:\n{body}    0\n"));
        assert!(msg.contains(crate::hir::LOWERING_TYPE_ERROR_TAG), "{body}{msg}");
        assert!(msg.contains(&format!("{slot} is declared as `i64` but receives `f64`")), "{body}{msg}");
    }
    // A float slot, or an untyped one, takes the promoted join.
    for body in ["    val r: f64 = if c: 1 else: 2.5\n", "    var r = 0.5\n    r = if c: 1 else: 2.5\n"] {
        parse_and_lower(&format!("fn probe(c: bool, n: i64) -> i64:\n{body}    0\n")).unwrap_or_else(|e| panic!("{body}{e}"));
    }
}

#[test]
fn nested_empty_literals_are_weak_at_every_depth() {
    for body in [
        "    val r = if c: [[]] else: xs\n",
        "    val r = if c: xs else: [[], []]\n",
        "    val r = match n:\n        case 0: ts\n        case _: [[]]\n",
        "    val r = match c:\n        case true: ts\n        case false: [[]]\n",
        "    val r = match n:\n        case 0: [[]]\n        case 1: [[], []]\n        case _: ts\n",
        "    val r = if c: [] else: xs\n",
    ] {
        let source = format!("fn probe(c: bool, n: i64, xs: [[f64]], ts: [[text]], fs: [f64]) -> i64:\n{body}    0\n");
        parse_and_lower(&source).unwrap_or_else(|e| panic!("must lower:\n{body}{e}"));
    }
    // Still judged above the hollow depth, and for populated inner arrays.
    for body in [
        "    val r = if c: [[]] else: fs\n",
        "    val r = if c: [[1]] else: xs\n",
        "    val r = match n:\n        case 0: ts\n        case 1: [[]]\n        case _: xs\n",
    ] {
        let msg = join_error(&format!("fn probe(c: bool, n: i64, xs: [[f64]], ts: [[text]], fs: [f64]) -> i64:\n{body}    0\n"));
        assert!(msg.contains("value arms disagree"), "{body}{msg}");
    }
}

#[test]
fn nested_hollow_then_arm_takes_the_concrete_sibling_type() {
    let module = parse_and_lower("fn probe(c: bool, xs: [[f64]]) -> i64:\n    val r = if c: [[]] else: xs\n    0\n").unwrap();
    let Some(HirType::Array { element, .. }) = local_ty(&module, "probe", "r") else { panic!("r must be an array") };
    assert!(matches!(module.types.get(element), Some(HirType::Array { element, .. }) if *element == TypeId::F64));
}

// A return type borrowed by the untyped-receiver suffix search is a guess. In
// both declaration orders one of `A.pos` / `B.pos` (tie-length names) is the
// float one; the float-into-int errors and the int/float join must not fire
// on it, whichever the tie-break picks.
#[test]
fn guessed_float_method_return_never_triggers_float_into_int_errors() {
    for (first, second) in [("f64", "i64"), ("i64", "f64")] {
        let classes = format!(
            "class A:\n    v: {first}\n    fn pos() -> {first}:\n        self.v\nclass B:\n    w: {second}\n    fn pos() -> {second}:\n        self.w\nfn t(i: i64) -> i64:\n    i\n"
        );
        for body in [
            "    val xs = [10, 20, 30]\n    xs[o.pos()]\n",
            "    val xs = [10, 20, 30]\n    val p = o.pos()\n    xs[p]\n",
            "    val r: i64 = if c: o.pos() else: 5\n    r\n",
            "    t(o.pos())\n",
        ] {
            let source = format!("{classes}fn probe(o, c: bool) -> i64:\n{body}");
            let lowered = super::parse_and_lower_lenient(&source);
            lowered.unwrap_or_else(|e| panic!("{first}/{second} must lower:\n{body}{e}"));
        }
    }
    // The guess does not leak into the next function.
    let source = "class A:\n    v: f64\n    fn pos() -> f64:\n        self.v\nfn g(o) -> f64:\n    o.pos()\nfn probe(c: bool) -> i64:\n    val r: i64 = if c: 1 else: 2.5\n    r\n";
    let msg = super::parse_and_lower_lenient(source).err().map(|e| e.to_string()).unwrap_or_default();
    assert!(msg.contains("binding `r` is declared as `i64` but receives `f64`"), "{msg}");
}
