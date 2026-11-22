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
        ("if flag: [1] else: words", TypeId::I64),
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
