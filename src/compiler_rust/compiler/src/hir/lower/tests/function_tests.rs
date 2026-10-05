use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;
use std::collections::HashMap;
use std::sync::Arc;

#[test]
fn test_lower_simple_function() {
    let module = parse_and_lower("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

    assert_eq!(module.functions.len(), 1);
    let func = &module.functions[0];
    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 2);
    assert_eq!(func.return_type, TypeId::I64);
}

#[test]
fn test_basic_types() {
    // Test basic types: i64, str, bool, f64
    let module = parse_and_lower("fn greet(name: str) -> i64:\n    let x: i64 = 42\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params[0].ty, TypeId::STRING);
    assert_eq!(func.return_type, TypeId::I64);
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn declared_return_type_rejects_explicit_and_implicit_mismatches() {
    for source in [
        "fn wrong() -> bool:\n    return \"not-a-bool\"\n",
        "fn wrong() -> bool:\n    \"not-a-bool\"\n",
    ] {
        let error = parse_and_lower(source).expect_err("declared bool return must reject text");
        assert!(
            matches!(
                error,
                LowerError::TypeMismatch {
                    expected: TypeId::BOOL,
                    found: TypeId::STRING
                }
            ),
            "unexpected diagnostic: {error:?}"
        );
    }
}

#[test]
fn declared_return_type_accepts_same_name_struct_across_registration_paths() {
    // TypeIds are module-registry-local (every HirModule owns its own
    // TypeRegistry; `register` always allocates a fresh id, and imported
    // named types are re-registered per module), so a declared `-> Pair`
    // and a returned Pair value can carry DIFFERENT TypeIds for the same
    // nominal type -- the day the declared-return check landed, raw
    // TypeId equality rejected 542 previously valid app files. Named
    // aggregates must compare by name, not by registry-local id. This
    // fixture pins the accepted case; cross-module import re-registration
    // is exercised by the full bootstrap closure.
    let source = "fn make() -> Pair:\n    return Pair{a: 1, b: 2}\n";
    let mut parser = simple_parser::Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([(
        "Pair".to_string(),
        vec![
            ("a".to_string(), simple_parser::Type::Simple("i64".to_string())),
            ("b".to_string(), simple_parser::Type::Simple("i64".to_string())),
        ],
    )])));

    let lowered = lowerer
        .lower_module(&module)
        .expect("same-name struct return across registration paths must be accepted");
    assert_eq!(lowered.functions.len(), 1);
}

#[test]
fn declared_return_type_accepts_gradual_array_and_void_forms() {
    // Gradual-typing corners the self-hosted reference compiler and the
    // interpreter have always admitted (and the pre-check seed admitted
    // too): a fixed-size literal returned against a dynamic array
    // declaration, a value body under an explicit `-> unit`, and a void
    // statement tail under a value declaration.
    for (source, case) in [
        (
            "fn fixed() -> [i64]:\n    [1, 2, 3]\n",
            "fixed literal against dynamic array declaration",
        ),
        ("fn unit_tail() -> unit:\n    42\n", "value body under explicit unit"),
    ] {
        lowerer_accepts(source, case);
    }
}

fn lowerer_accepts(source: &str, case: &str) {
    let lowered = parse_and_lower(source).unwrap_or_else(|error| panic!("{case}: {error:?}"));
    assert_eq!(lowered.functions.len(), 1, "{case}");
}

#[test]
fn test_lower_function_with_locals() {
    let module = parse_and_lower("fn compute(x: i64) -> i64:\n    let y: i64 = x * 2\n    return y\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 1);
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "y");
}

#[test]
fn test_multiple_functions() {
    let module = parse_and_lower(
        "fn foo() -> i64:\n    return 1\n\nfn bar() -> i64:\n    return 2\n\nfn baz() -> i64:\n    return 3\n",
    )
    .unwrap();

    assert_eq!(module.functions.len(), 3);
    assert_eq!(module.functions[0].name, "foo");
    assert_eq!(module.functions[1].name, "bar");
    assert_eq!(module.functions[2].name, "baz");
}

#[test]
fn test_function_with_multiple_params() {
    let module = parse_and_lower("fn multi(a: i64, b: f64, c: str, d: bool) -> i64:\n    return a\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 4);
    assert_eq!(func.params[0].ty, TypeId::I64);
    assert_eq!(func.params[1].ty, TypeId::F64);
    assert_eq!(func.params[2].ty, TypeId::STRING);
    assert_eq!(func.params[3].ty, TypeId::BOOL);
}

#[test]
fn extern_call_preserves_declared_optional_array_return_type() {
    let source = r#"
extern fn snapshot() -> [(text, text)]?

fn snapshot_len() -> i64:
    val entries = snapshot() ?? []
    var seen = 0
    for entry in entries:
        val (key, value) = entry
        if key.len() >= 0 and value.len() >= 0:
            seen = seen + 1
    entries.len() + seen
"#;
    parse_and_lower(source).expect("declared extern return type must survive calls, coalescing, len, and iteration");
}

#[test]
fn unannotated_value_function_uses_tagged_any_return_instead_of_void() {
    let module = parse_and_lower(
        "fn no_ret_type(data: [i64], index: i64):\n    data[index]\n\nfn caller() -> i64:\n    no_ret_type([7, 8, 9], 1)\n",
    )
    .expect("unannotated value function must lower");

    let callee = module
        .functions
        .iter()
        .find(|function| function.name == "no_ret_type")
        .unwrap();
    assert_eq!(callee.return_type, TypeId::ANY);
    assert!(matches!(callee.body.last(), Some(HirStmt::Expr(expr)) if expr.ty == TypeId::I64));
}

#[test]
fn unannotated_procedure_remains_void() {
    let module = parse_and_lower("fn procedure():\n    val value = 1\n").expect("procedure must lower");
    assert_eq!(module.functions[0].return_type, TypeId::VOID);
}

// Single-argument `Result<T>` used to resolve to ANY (only the 2-argument form
// was instantiated), erasing the Ok payload: `val s = f()?; s.first` then had
// an ANY receiver and, with `first` spelled by two layouts, failed to lower --
// a whole-program de-JIT (h1_client.parse_http_response_bytes, 2026-10-04).
#[test]
fn single_arg_result_try_keeps_ok_payload_type() {
    let source = "class P:\n    first: i64\n    second: text\n\nclass Q:\n    zero: i64\n    first: text\n\nfn make(v: i64) -> Result<P>:\n    Ok(P(first: v, second: \"s\"))\n\nfn use_it() -> Result<i64, text>:\n    val p = make(3)?\n    Ok(p.first)\n";
    let module = parse_and_lower(source).expect("`?` on Result<T> must keep T so `.first` resolves");
    let make = module.functions.iter().find(|f| f.name == "make").unwrap();
    match module.types.get(make.return_type) {
        Some(crate::hir::HirType::Enum { name, variants, .. }) => {
            assert_eq!(name, "Result");
            let ok = variants.iter().find(|(v, _)| v == "Ok").and_then(|(_, p)| p.as_ref());
            let ok_ty = ok.and_then(|fields| fields.first()).copied().unwrap();
            assert!(matches!(module.types.get(ok_ty), Some(crate::hir::HirType::Struct { name, .. }) if name == "P"));
            let err = variants.iter().find(|(v, _)| v == "Err").and_then(|(_, p)| p.as_ref());
            assert_eq!(err.and_then(|fields| fields.first()).copied(), Some(TypeId::ANY));
        }
        other => panic!("Result<P> must resolve to the Result enum, got {other:?}"),
    }
}

// Generalization: `!` on Result<T> (the JIT used to hand the Result wrapper
// through as the value) and on Option<T>, in the same ambiguous-field setting.
#[test]
fn single_arg_result_force_unwrap_keeps_ok_payload_type() {
    let source = "class P:\n    first: i64\n    second: text\n\nclass Q:\n    zero: i64\n    first: text\n\nfn make(v: i64) -> Result<P>:\n    Ok(P(first: v, second: \"s\"))\n\nfn maybe(v: i64) -> Option<P>:\n    Some(P(first: v, second: \"s\"))\n\nfn use_it() -> i64:\n    make(1)!.first + maybe(2)!.first\n";
    parse_and_lower(source).expect("`!` on Result<T>/Option<T> must keep T so `.first` resolves");
}

fn dynamic_init_source(count: usize) -> String {
    // Every global is initialized by a CALL that reads the previous global, so
    // each one is a genuine dynamic initializer and order matters.
    let mut source = String::from("fn bump(x: i64) -> i64:\n    x + 1\n\nval g_0 = bump(0)\n");
    for i in 1..count {
        source.push_str(&format!("val g_{i} = bump(g_{})\n", i - 1));
    }
    source
}

fn assigned_globals(function: &HirFunction) -> Vec<String> {
    function
        .body
        .iter()
        .filter_map(|stmt| match stmt {
            HirStmt::Assign { target, .. } => match &target.kind {
                HirExprKind::Global(name) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

// A large dynamic-init set is split into bounded `__dyninit_part_<i>`
// functions that the single `__module_init_dynamic` root calls in order, so
// declaration order -- and therefore cross-global dependencies -- is preserved.
#[test]
fn dynamic_module_init_is_chunked_in_declaration_order() {
    let chunk = Lowerer::DYNAMIC_INIT_CHUNK;
    let count = chunk * 2 + 7;
    let module = parse_and_lower(&dynamic_init_source(count)).expect("chunked init must lower");
    let roots: Vec<_> = module
        .functions
        .iter()
        .filter(|f| f.name.starts_with("__module_init_"))
        .collect();
    assert_eq!(roots.len(), 1, "exactly one init root");
    let called: Vec<String> = roots[0]
        .body
        .iter()
        .filter_map(|stmt| match stmt {
            HirStmt::Expr(HirExpr {
                kind: HirExprKind::Call { func, .. },
                ..
            }) => match &func.kind {
                HirExprKind::Global(name) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    assert_eq!(called, vec!["__dyninit_part_0", "__dyninit_part_1", "__dyninit_part_2"]);
    let mut order: Vec<String> = Vec::new();
    for part in &called {
        let function = module.functions.iter().find(|f| &f.name == part).expect("part exists");
        let assigned = assigned_globals(function);
        assert!(assigned.len() <= chunk, "part {part} exceeds the chunk bound");
        order.extend(assigned);
    }
    let expected: Vec<String> = (0..count).map(|i| format!("g_{i}")).collect();
    assert_eq!(order, expected, "parts must assign globals in declaration order");
}

fn repeat_kind(source: &str) -> &'static str {
    let module = parse_and_lower(source).expect("repeat must lower");
    let f = module.functions.iter().find(|f| f.name == "make").expect("make");
    match f.body.first() {
        Some(HirStmt::Let { value: Some(v), .. }) | Some(HirStmt::Expr(v)) | Some(HirStmt::Return(Some(v))) => {
            match &v.kind {
                HirExprKind::ArrayRepeat { .. } => "fill",
                HirExprKind::Array(_) => "unrolled",
                _ => "other",
            }
        }
        _ => "other",
    }
}

// Repro: `[_KERN_EMPTY; 72200]` (pure scalar global, huge count) was unrolled
// into a 72,200-element literal -- 144k MIR instructions, ~20 min of Cranelift.
#[test]
fn large_pure_scalar_repeat_stays_runtime_fill() {
    let src = "val K: i32 = 7\n\nfn make() -> [i32]:\n    return [K; 72200]\n";
    assert_eq!(repeat_kind(src), "fill");
    let src = "fn make() -> [i64]:\n    return [-5; 300]\n";
    assert_eq!(repeat_kind(src), "fill");
}

// Generalization: everything whose meaning depends on per-element evaluation
// or on the literal path stays unrolled -- small counts, heap elements (a fill
// would alias one object), u8 (packed literal path) and u64 (a full-width u64
// fill reads back wrong through rt_array_repeat).
#[test]
fn repeat_unrolls_when_a_fill_could_change_meaning() {
    assert_eq!(repeat_kind("fn make() -> [i64]:\n    return [0; 8]\n"), "unrolled");
    assert_eq!(repeat_kind("fn make() -> [[i64]]:\n    return [[0, 0]; 300]\n"), "unrolled");
    assert_eq!(repeat_kind("fn make() -> [u8]:\n    return [0u8; 300]\n"), "unrolled");
    assert_eq!(repeat_kind("fn make() -> [u64]:\n    return [1u64; 300]\n"), "unrolled");
}

// Generalization: a module that fits in one chunk keeps the historical single
// `__module_init_dynamic` with every assignment inline (no parts emitted).
#[test]
fn small_dynamic_module_init_stays_single_function() {
    let module = parse_and_lower(&dynamic_init_source(5)).expect("small init must lower");
    assert!(!module.functions.iter().any(|f| f.name.starts_with("__dyninit_part_")));
    let root = module
        .functions
        .iter()
        .find(|f| f.name == "__module_init_dynamic")
        .expect("root");
    assert_eq!(
        assigned_globals(root),
        (0..5).map(|i| format!("g_{i}")).collect::<Vec<_>>()
    );
}
