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

/// optional_return_into_scalar_fn_accepted_2026-11-26: a declared `T?` (or
/// `Dict.get`) returned from `-> T` is a type error.
#[test]
fn optional_returned_from_scalar_fn_is_rejected() {
    for source in [
        "fn maybe() -> i64?:\n    return Some(7)\n\nfn value() -> i64:\n    return maybe()\n",
        "fn lookup() -> i64:\n    val map: Dict<i64, i64> = {1: 7}\n    return map.get(1)\n",
        "fn lookup() -> i64:\n    val map: Dict<i64, i64> = {1: 7}\n    map.get(1)\n",
    ] {
        let error = parse_and_lower(source).expect_err("T? returned from -> T must reject");
        assert!(format!("{error:?}").contains("error[E1003]"), "unexpected diagnostic: {error:?}");
    }
    parse_and_lower("fn lookup() -> i64:\n    val map: Dict<i64, i64> = {1: 7}\n    return map.get(1) ?? 0\n")
        .expect("unwrapped Dict.get must lower");
}

/// Fable review 2026-11-26: on an untyped receiver the seed borrows a return
/// type from any same-named user method (`A.join() -> text?`). That guess must
/// not make `-> text` reject `xs.join(",")` or `a.concat(b).join(",")`.
#[test]
fn optional_rule_ignores_untyped_receiver_suffix_guess() {
    let class = "class A:\n    n: text\n    fn join(sep: text) -> text?:\n        Some(self.n + sep)\n\n";
    for body in [
        "fn f<T>(xs: T) -> text:\n    xs.join(\",\")\n",
        "fn f<T>(xs: T) -> text:\n    return xs.join(\",\")\n",
        "fn f<T>(a: T, b: T) -> text:\n    a.concat(b).join(\",\")\n",
        "fn f<T>(xs: T) -> text:\n    val joined = xs.join(\",\")\n    joined\n",
    ] {
        parse_and_lower(&format!("{class}{body}")).unwrap_or_else(|e| panic!("{body}: {e:?}"));
    }
}

/// A guess earlier in the module must not exempt a real declared `T?`.
#[test]
fn optional_rule_guess_does_not_mask_declared_optional() {
    let prefix = "class A:\n    n: text\n    fn join(sep: text) -> text?:\n        Some(self.n + sep)\n\n\
                  fn m() -> text?:\n    Some(\"x\")\n\nfn f<T>(xs: T) -> text:\n    xs.join(\",\")\n\n";
    for body in ["fn g(a: A) -> text:\n    a.join(\",\")\n", "fn v() -> text:\n    m()\n"] {
        let error = parse_and_lower(&format!("{prefix}{body}")).expect_err(body);
        assert!(format!("{error:?}").contains("error[E1003]"), "{body}: {error:?}");
    }
}

/// Fable re-review 2026-11-26: the `Option<T>` spelling of the guess is
/// skipped too, and a declared `Option<T>` is still rejected.
#[test]
fn optional_rule_handles_option_enum_spelling() {
    let class = "class A:\n    n: text\n    fn join(sep: text) -> Option<text>:\n        Some(self.n + sep)\n\n";
    for body in [
        "fn f<T>(xs: T) -> text:\n    xs.join(\",\")\n",
        "fn f(a: [text], b: [text]) -> text:\n    a.concat(b).join(\",\")\n",
    ] {
        parse_and_lower(&format!("{class}{body}")).unwrap_or_else(|e| panic!("{body}: {e:?}"));
    }
    let error = parse_and_lower(&format!("{class}fn g(a: A) -> text:\n    a.join(\",\")\n")).expect_err("declared Option<text>");
    assert!(format!("{error:?}").contains("error[E1003]"), "{error:?}");
}

/// An Option of a different payload is still an Option word in a scalar
/// slot: `Option<f64>` into `-> i64` and `i64?` into `-> text` must reject.
#[test]
fn optional_rule_rejects_mismatched_payloads() {
    for source in [
        "fn m() -> Option<f64>:\n    Some(1.5)\n\nfn f() -> i64:\n    return m()\n",
        "fn m() -> i64?:\n    None\n\nfn f() -> text:\n    return m()\n",
    ] {
        let error = parse_and_lower(source).expect_err(source);
        assert!(format!("{error:?}").contains("error[E1003]"), "{source}: {error:?}");
    }
}

/// Sweep 2026-11-26 (option_fn_transport_siblings_spec): `if val f = self.cb`
/// leaves a class-field `Option<fn>` binding typed `(fn)?`; calling it returns
/// the function's `text`, not an Option.
#[test]
fn calling_unnarrowed_optional_fn_binding_returns_its_result_type() {
    let source = "class Holder:\n    cb: Option<fn(text, text) -> text>\n\n    fn run(a: text, b: text) -> text:\n        \
                  if val f = self.cb:\n            return f(a, b)\n        \"none\"\n";
    parse_and_lower(source).unwrap_or_else(|e| panic!("{e:?}"));
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

#[test]
fn extern_abi_system_attribute_is_recorded_only_for_tagged_externs() {
    let module = parse_and_lower(
        "@abi(\"system\")\nextern fn Sleep(ms: u32)\n@abi(\"system\")\nextern fn GetLastError() -> u32\nextern fn plain_c(x: i32) -> i32\nfn test() -> i64:\n    0\n",
    )
    .unwrap();

    let sleep = module.extern_system_abi.get("Sleep").expect("Sleep recorded");
    assert_eq!(sleep.0, vec![TypeId::U32]);
    assert_eq!(sleep.1, TypeId::VOID);
    let last = module.extern_system_abi.get("GetLastError").expect("GetLastError recorded");
    assert!(last.0.is_empty());
    assert_eq!(last.1, TypeId::U32);
    assert!(!module.extern_system_abi.contains_key("plain_c"));
    assert!(module.extern_param_types.contains_key("plain_c"));
}

/// seed_jit_u8_array_into_i64_array_param_reads_zero_2026-11-27: a `[u8]`
/// array bound to a `[i64]` parameter is read with the wrong element width
/// under the JIT (255 reads back as 0). The language has no array element
/// coercion, so a byte-packed `[u8]` into another numeric element type is an
/// E1003 type error.
#[test]
fn array_param_rejects_u8_array_into_wider_element_type() {
    let callee = "fn at64(data: [i64], i: i64) -> i64:\n    data[i]\n\n";
    for call in [
        "fn f() -> i64:\n    val b: [u8] = [1u8, 255u8]\n    at64(b, 1)\n",
        "fn f(b: [u8]) -> i64:\n    at64(b, 0)\n",
    ] {
        let error = parse_and_lower(&format!("{callee}{call}")).expect_err(call);
        assert!(format!("{error:?}").contains("error[E1003]"), "{call}: {error:?}");
    }
    for call in [
        "fn f(b: [i64]) -> i64:\n    at64(b, 0)\n",
        "fn f() -> i64:\n    at64([1, 2, 3], 0)\n",
    ] {
        parse_and_lower(&format!("{callee}{call}")).unwrap_or_else(|e| panic!("{call}: {e:?}"));
    }
    let bytes = "fn first(data: [u8]) -> i64:\n    data[0]\n\nfn f() -> i64:\n    first([0, 1, 2])\n";
    parse_and_lower(bytes).unwrap_or_else(|e| panic!("literal into [u8]: {e:?}"));
}

/// Shape 1: the callee is declared after the caller, so its HIR value type is
/// not yet a `Function` and only the recorded parameter row is known.
#[test]
fn array_param_rejects_u8_array_into_later_declared_callee() {
    let tail = "\nfn at64(data: [i64], i: i64) -> i64:\n    data[i]\n\nfn atl(data: List<u32>) -> i64:\n    0\n\nfn first(data: [u8]) -> i64:\n    data[0]\n";
    for call in [
        "fn f(b: [u8]) -> i64:\n    at64(b, 0)\n",
        "fn f(b: [u8]) -> i64:\n    atl(b)\n",
    ] {
        let error = parse_and_lower(&format!("{call}{tail}")).expect_err(call);
        assert!(format!("{error:?}").contains("error[E1003]"), "{call}: {error:?}");
    }
    for call in [
        "fn f(b: [i64]) -> i64:\n    at64(b, 0)\n",
        "fn f(b: [u8]) -> i64:\n    first(b)\n",
        "fn f() -> i64:\n    at64([1, 2], 0)\n",
    ] {
        parse_and_lower(&format!("{call}{tail}")).unwrap_or_else(|e| panic!("{call}: {e:?}"));
    }
}

/// Shape 2: instance, `self.`, static and impl-block methods whose parameter
/// is spelled `[i64]`.
#[test]
fn array_param_rejects_u8_array_into_method_parameter() {
    let decls = "class Box:\n    var n: i64\n    fn at(data: [i64], i: i64) -> i64:\n        data[i]\n    fn own(b: [u8]) -> i64:\n        self.at(b, 0)\n    static fn sat(data: [i64]) -> i64:\n        data[0]\n\nstruct P:\n    n: i64\n\nimpl P:\n    fn pat(data: [i64]) -> i64:\n        data[0]\n\n";
    let decls_ok = decls.replace("        self.at(b, 0)", "        0");
    for call in [
        "fn f(bx: Box, b: [u8]) -> i64:\n    bx.at(b, 0)\n",
        "fn f(b: [u8]) -> i64:\n    Box.sat(b)\n",
        "fn f(p: P, b: [u8]) -> i64:\n    p.pat(b)\n",
    ] {
        let error = parse_and_lower(&format!("{decls_ok}{call}")).expect_err(call);
        assert!(format!("{error:?}").contains("error[E1003]"), "{call}: {error:?}");
    }
    let error = parse_and_lower(decls).expect_err("self.at");
    assert!(format!("{error:?}").contains("error[E1003]"), "self.at: {error:?}");
    for call in [
        "fn f(bx: Box, b: [i64]) -> i64:\n    bx.at(b, 0)\n",
        "fn f(b: [i64]) -> i64:\n    Box.sat(b)\n",
        "fn f(p: P) -> i64:\n    p.pat([1, 2])\n",
    ] {
        parse_and_lower(&format!("{decls_ok}{call}")).unwrap_or_else(|e| panic!("{call}: {e:?}"));
    }
}

/// Shape 3: a trait-typed receiver, with no float argument in the call.
#[test]
fn array_param_rejects_u8_array_into_trait_method_parameter() {
    // `keep_words`, not a builtin collection name such as `put`: a builtin
    // name is taken by the builtin method lowering before the trait row is
    // consulted (follow-up u8_array_into_word_array_unchecked_slots_2026-11-28).
    let decls = "trait Store:\n    fn keep_words(data: [i64]) -> i64\n\n";
    let bad = format!("{decls}fn f(s: Store, b: [u8]) -> i64:\n    s.keep_words(b)\n");
    let error = parse_and_lower(&bad).expect_err("trait");
    assert!(format!("{error:?}").contains("error[E1003]"), "trait: {error:?}");
    let good = format!("{decls}fn f(s: Store, b: [i64]) -> i64:\n    s.keep_words(b)\n");
    parse_and_lower(&good).unwrap_or_else(|e| panic!("trait [i64]: {e:?}"));
}
