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
    // jit_const_size_u8_repeat_literal_blowup_2026-11-27: a constant-size u8
    // repeat must not unroll into an N-element literal either.
    let src = "fn make() -> [u8]:\n    return [0u8; 16777216]\n";
    assert_eq!(repeat_kind(src), "fill");
    let src = "fn make() -> [u8]:\n    return [7u8; 300]\n";
    assert_eq!(repeat_kind(src), "fill");
}

// Generalization: everything whose meaning depends on per-element evaluation
// or on the literal path stays unrolled -- small counts, heap elements (a fill
// would alias one object) and u64 (a full-width u64 fill reads back wrong
// through rt_array_repeat).
#[test]
fn repeat_unrolls_when_a_fill_could_change_meaning() {
    assert_eq!(repeat_kind("fn make() -> [i64]:\n    return [0; 8]\n"), "unrolled");
    assert_eq!(repeat_kind("fn make() -> [[i64]]:\n    return [[0, 0]; 300]\n"), "unrolled");
    assert_eq!(repeat_kind("fn make() -> [u8]:\n    return [0u8; 8]\n"), "unrolled");
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

/// u8_array_into_word_array_unchecked_slots_2026-11-28: every `bad` source
/// must fail with the E1003 `[u8]` diagnostic and every `good` one must
/// lower. All offenders are reported together.
fn assert_u8_word_slot_cases(bad: &[(&str, &str)], good: &[(&str, &str)]) {
    let mut wrong = Vec::new();
    for (label, src) in bad {
        match parse_and_lower(src) {
            Err(e) if format!("{e:?}").contains("error[E1003]") && format!("{e:?}").contains("u8]") => {}
            Err(e) => wrong.push(format!("{label}: expected the E1003 [u8] diagnostic, got {e:?}")),
            Ok(_) => wrong.push(format!("{label}: expected E1003, but it lowered")),
        }
    }
    for (label, src) in good {
        if let Err(e) = parse_and_lower(src) {
            wrong.push(format!("{label}: must lower, got {e:?}"));
        }
    }
    assert!(wrong.is_empty(), "\n{}", wrong.join("\n"));
}

/// Slot 1: a binding with a declared word-array type, initialised or
/// reassigned from a `[u8]`.
#[test]
fn u8_array_rejected_in_annotated_let_and_assignment() {
    assert_u8_word_slot_cases(
        &[
            ("val", "fn f(b: [u8]) -> i64:\n    val w: [i64] = b\n    w[0]\n"),
            ("var", "fn f(b: [u8]) -> i64:\n    var w: [u32] = b\n    0\n"),
            ("List", "fn f(b: [u8]) -> i64:\n    val w: List<i64> = b\n    w[0]\n"),
            ("reassign", "fn f(b: [u8]) -> i64:\n    var w: [i64] = [1, 2]\n    w = b\n    w[0]\n"),
        ],
        &[
            ("literal", "fn f() -> i64:\n    val w: [i64] = [1, 2]\n    w[0]\n"),
            ("same", "fn f(b: [u8]) -> i64:\n    val w: [u8] = b\n    0\n"),
            ("words", "fn f(a: [i64]) -> i64:\n    var w: [i64] = [1]\n    w = a\n    w[0]\n"),
            ("word into u8 slot", "fn f(a: [i64]) -> i64:\n    val w: [u8] = a\n    0\n"),
            ("map", "fn f(b: [u8]) -> i64:\n    val w: [i64] = b.map(\\x: x as i64)\n    w[0]\n"),
            ("untyped empty", "fn f(b: [u8]) -> i64:\n    var w = []\n    w = b\n    0\n"),
            ("inferred", "fn f(b: [u8]) -> i64:\n    val w = b\n    0\n"),
        ],
    );
}

/// Slot 2: a `[u8]` returned where a word array is declared, by `return`
/// and by the implicit tail.
#[test]
fn u8_array_rejected_in_return() {
    assert_u8_word_slot_cases(
        &[
            ("return", "fn g(b: [u8]) -> [i64]:\n    return b\n"),
            ("tail", "fn g(b: [u8]) -> [i64]:\n    b\n"),
            ("List", "fn g(b: [u8]) -> List<u16>:\n    return b\n"),
            ("if tail", "fn g(b: [u8], c: bool) -> [i64]:\n    if c:\n        b\n    else:\n        [1, 2]\n"),
        ],
        &[
            ("same", "fn g(b: [u8]) -> [u8]:\n    return b\n"),
            ("literal", "fn g() -> [i64]:\n    return [1, 2]\n"),
            ("literal tail", "fn g() -> [i64]:\n    [1, 2]\n"),
            ("words", "fn g(a: [i64]) -> [i64]:\n    a\n"),
            ("map", "fn g(b: [u8]) -> [i64]:\n    return b.map(\\x: x as i64)\n"),
            ("map tail", "fn g(b: [u8]) -> [i64]:\n    b.map(\\x: x as i64)\n"),
        ],
    );
}

/// Slot 3: a `[u8]` stored into a struct/class field typed as a word array,
/// by construction and by assignment.
#[test]
fn u8_array_rejected_in_field_init_and_assignment() {
    let st = "struct W:\n    words: [i64]\n    n: i64\n\n";
    let cl = "class C:\n    var words: List<i64>\n    me set(b: [u8]):\n        self.words = b\n    me set_words(a: [i64]):\n        self.words = a\n\n";
    let cl_ok = cl.replace("        self.words = b\n", "        self.words = []\n");
    assert_u8_word_slot_cases(
        &[
            ("struct named", &format!("{st}fn f(b: [u8]) -> W:\n    W(words: b, n: 1)\n")),
            ("struct positional", &format!("{st}fn f(b: [u8]) -> W:\n    W(b, 1)\n")),
            ("class init", &format!("{cl_ok}fn f(b: [u8]) -> C:\n    C(words: b)\n")),
            ("self field assign", cl),
            ("field assign", &format!("{st}fn f(b: [u8]) -> i64:\n    var w = W(words: [1], n: 1)\n    w.words = b\n    0\n")),
        ],
        &[
            ("struct words", &format!("{st}fn f(a: [i64]) -> W:\n    W(words: a, n: 1)\n")),
            ("struct literal", &format!("{st}fn f() -> W:\n    W(words: [1, 2], n: 1)\n")),
            ("class ok", &format!("{cl_ok}fn f(a: [i64]) -> C:\n    C(words: a)\n")),
            ("field assign words", &format!("{st}fn f(a: [i64]) -> i64:\n    var w = W(words: [1], n: 1)\n    w.words = a\n    0\n")),
        ],
    );
}

/// Slot 4: an optional word array, `[i64]?`.
#[test]
fn u8_array_rejected_in_optional_word_array_slot() {
    let early = "fn at(data: [i64]?) -> i64:\n    0\n\n";
    let late = "\nfn at(data: [i64]?) -> i64:\n    0\n";
    assert_u8_word_slot_cases(
        &[
            ("param", &format!("{early}fn f(b: [u8]) -> i64:\n    at(b)\n")),
            ("later-declared param", &format!("fn f(b: [u8]) -> i64:\n    at(b)\n{late}")),
            ("let", "fn f(b: [u8]) -> i64:\n    val w: [i64]? = b\n    0\n"),
            ("return", "fn g(b: [u8]) -> [i64]?:\n    return b\n"),
        ],
        &[
            ("words", &format!("{early}fn f(a: [i64]) -> i64:\n    at(a)\n")),
            ("later-declared words", &format!("fn f(a: [i64]) -> i64:\n    at(a)\n{late}")),
            ("nil", &format!("{early}fn f() -> i64:\n    at(nil)\n")),
            ("literal", &format!("{early}fn f() -> i64:\n    at([1, 2])\n")),
            ("u8 optional", "fn f(b: [u8]) -> i64:\n    val w: [u8]? = b\n    0\n"),
        ],
    );
}

/// Slot 5: nested arrays, `[[u8]]` into `[[i64]]`, including a literal
/// whose element is a `[u8]`.
#[test]
fn u8_array_rejected_in_nested_word_array_slot() {
    let early = "fn rows(data: [[i64]]) -> i64:\n    0\n\n";
    let late = "\nfn rows(data: [[i64]]) -> i64:\n    0\n";
    assert_u8_word_slot_cases(
        &[
            ("param", &format!("{early}fn f(bb: [[u8]]) -> i64:\n    rows(bb)\n")),
            ("later-declared param", &format!("fn f(bb: [[u8]]) -> i64:\n    rows(bb)\n{late}")),
            ("let", "fn f(bb: [[u8]]) -> i64:\n    val w: [[i64]] = bb\n    0\n"),
            ("return", "fn g(bb: [[u8]]) -> [[i64]]:\n    return bb\n"),
            ("literal of u8 rows", "fn f(b: [u8]) -> i64:\n    val w: [[i64]] = [b]\n    0\n"),
            ("literal of u8 rows param", &format!("{early}fn f(b: [u8]) -> i64:\n    rows([b, b])\n")),
        ],
        &[
            ("words", &format!("{early}fn f(aa: [[i64]]) -> i64:\n    rows(aa)\n")),
            ("same", "fn f(bb: [[u8]]) -> i64:\n    val w: [[u8]] = bb\n    0\n"),
            ("literal rows", &format!("{early}fn f() -> i64:\n    rows([[1, 2], [3]])\n")),
            ("literal of word rows", &format!("{early}fn f(a: [i64]) -> i64:\n    rows([a])\n")),
            ("literal of u8 rows into u8", "fn f(b: [u8]) -> i64:\n    val w: [[u8]] = [b]\n    0\n"),
        ],
    );
}

/// Slot 6: a user method whose name is also a builtin collection method
/// (`put`, `push`), on a trait-typed and on a class-typed receiver.
#[test]
fn u8_array_rejected_in_builtin_named_method() {
    let tr = "trait Store:\n    fn put(data: [i64]) -> i64\n    fn push(data: [i64]) -> i64\n\n";
    let cl = "class Bag:\n    var n: i64\n    fn push(data: [i64]) -> i64:\n        data[0]\n    fn put(data: [i64]) -> i64:\n        data[0]\n\n";
    assert_u8_word_slot_cases(
        &[
            ("trait put", &format!("{tr}fn f(s: Store, b: [u8]) -> i64:\n    s.put(b)\n")),
            ("trait push", &format!("{tr}fn f(s: Store, b: [u8]) -> i64:\n    s.push(b)\n")),
            ("class push", &format!("{cl}fn f(g: Bag, b: [u8]) -> i64:\n    g.push(b)\n")),
            ("class put", &format!("{cl}fn f(g: Bag, b: [u8]) -> i64:\n    g.put(b)\n")),
        ],
        &[
            ("trait put words", &format!("{tr}fn f(s: Store, a: [i64]) -> i64:\n    s.put(a)\n")),
            ("trait push words", &format!("{tr}fn f(s: Store, a: [i64]) -> i64:\n    s.push(a)\n")),
            ("class push words", &format!("{cl}fn f(g: Bag, a: [i64]) -> i64:\n    g.push(a)\n")),
            ("builtin push of a byte", "fn f(b: [u8]) -> i64:\n    var out: [u8] = []\n    out.push(b[0])\n    0\n"),
            ("builtin push of u8 rows", "fn f(b: [u8]) -> i64:\n    var out: [[u8]] = []\n    out.push(b)\n    0\n"),
        ],
    );
}

/// Slot 7: the `[u8]` passed through a named argument.
#[test]
fn u8_array_rejected_in_named_argument() {
    let decls = "class Box:\n    var n: i64\n    fn at(data: [i64], i: i64) -> i64:\n        data[i]\n    static fn sat(data: [i64]) -> i64:\n        data[0]\n\ntrait Store:\n    fn keep_words(i: i64, data: [i64]) -> i64\n\nfn at64(data: [i64], i: i64) -> i64:\n    data[i]\n\n";
    assert_u8_word_slot_cases(
        &[
            ("method", &format!("{decls}fn f(bx: Box, b: [u8]) -> i64:\n    bx.at(data: b, i: 0)\n")),
            ("method reordered", &format!("{decls}fn f(bx: Box, b: [u8]) -> i64:\n    bx.at(i: 0, data: b)\n")),
            ("static", &format!("{decls}fn f(b: [u8]) -> i64:\n    Box.sat(data: b)\n")),
            ("trait", &format!("{decls}fn f(s: Store, b: [u8]) -> i64:\n    s.keep_words(data: b, i: 0)\n")),
            ("free fn", &format!("{decls}fn f(b: [u8]) -> i64:\n    at64(data: b, i: 0)\n")),
            ("free fn reordered", &format!("{decls}fn f(b: [u8]) -> i64:\n    at64(i: 0, data: b)\n")),
        ],
        &[
            ("method", &format!("{decls}fn f(bx: Box, a: [i64]) -> i64:\n    bx.at(data: a, i: 0)\n")),
            ("method reordered", &format!("{decls}fn f(bx: Box, a: [i64]) -> i64:\n    bx.at(i: 0, data: a)\n")),
            ("static", &format!("{decls}fn f(a: [i64]) -> i64:\n    Box.sat(data: a)\n")),
            ("trait", &format!("{decls}fn f(s: Store, a: [i64]) -> i64:\n    s.keep_words(data: a, i: 0)\n")),
            ("free fn", &format!("{decls}fn f(a: [i64]) -> i64:\n    at64(i: 0, data: a)\n")),
        ],
    );
}

/// An untyped `var x = []` that is never pushed to used to leave its local
/// index marked, so a declared `[u8]` local at the same index of the next
/// function was retyped to a word array by its first push (found by the
/// assignment-slot check in `gcm_gf128_mul`).
#[test]
fn untyped_empty_array_mark_does_not_leak_into_next_function() {
    let src = "fn a(p: i64, q: i64) -> i64:\n    var x = []\n    0\n\nfn f(n0: [u8], n1: [u8]) -> [u8]:\n    var z: [u8] = []\n    z.push(0x00)\n    z = n0\n    z\n";
    parse_and_lower(src).unwrap_or_else(|e| panic!("declared [u8] local retyped: {e:?}"));
}

/// Residual (1) of u8_array_into_word_array_residual_shapes_2026-11-28: the
/// VALUE is itself optional (`[u8]?`, or the `Option<[u8]>` enum spelling).
/// `is_u8_array_value` looked at the value's raw type, and an Optional is not
/// an Array, so the slot rule never fired and the byte-packed array reached
/// the word slot.
#[test]
fn u8_array_rejected_in_optional_value_into_word_slot() {
    let early = "fn at(data: [i64]?) -> i64:\n    0\n\n";
    assert_u8_word_slot_cases(
        &[
            ("let", "fn f(x: [u8]?) -> i64:\n    val w: [i64]? = x\n    0\n"),
            ("param", &format!("{early}fn f(x: [u8]?) -> i64:\n    at(x)\n")),
            ("return", "fn g(x: [u8]?) -> [i64]?:\n    return x\n"),
            ("nested", "fn f(x: [[u8]]?) -> i64:\n    val w: [[i64]]? = x\n    0\n"),
            ("Option enum value", "fn f(x: Option<[u8]>) -> i64:\n    val w: [i64]? = x\n    0\n"),
            ("unwrapped", "fn f(x: [u8]?) -> i64:\n    val w: [i64] = x.unwrap()\n    0\n"),
        ],
        &[
            ("same", "fn f(x: [u8]?) -> i64:\n    val w: [u8]? = x\n    0\n"),
            ("words", "fn f(x: [i64]?) -> i64:\n    val w: [i64]? = x\n    0\n"),
            ("nil", "fn f() -> i64:\n    val w: [i64]? = nil\n    0\n"),
            ("literal", &format!("{early}fn f() -> i64:\n    at([1, 2])\n")),
        ],
    );
}

/// Residual (2) of u8_array_into_word_array_residual_shapes_2026-11-28: a
/// parameter spelled `Option<[i64]>` (the Generic form, not `[T]?`).
/// `numeric_array_param_element` peeled only `Type::Optional`, so the
/// recorded word-array row was empty for every recorded row: a
/// later-declared callee, a method (via named arguments or an imported
/// owner) and a trait row.
#[test]
fn u8_array_rejected_in_option_generic_spelled_parameter() {
    let late = "\nfn at(data: Option<[i64]>) -> i64:\n    0\n";
    let bx = "class Box:\n    var n: i64\n    fn at(data: Option<[i64]>) -> i64:\n        0\n\n";
    let tr = "trait Store:\n    fn keep_words(data: Option<[i64]>) -> i64\n\n";
    assert_u8_word_slot_cases(
        &[
            ("later free fn", &format!("fn f(b: [u8]) -> i64:\n    at(b)\n{late}")),
            ("later free fn named", &format!("fn f(b: [u8]) -> i64:\n    at(data: b)\n{late}")),
            ("method", &format!("{bx}fn f(g: Box, b: [u8]) -> i64:\n    g.at(b)\n")),
            ("method named", &format!("{bx}fn f(g: Box, b: [u8]) -> i64:\n    g.at(data: b)\n")),
            ("trait", &format!("{tr}fn f(s: Store, b: [u8]) -> i64:\n    s.keep_words(b)\n")),
            ("trait builtin name", &format!("trait Store:\n    fn put(data: Option<[i64]>) -> i64\n\nfn f(s: Store, b: [u8]) -> i64:\n    s.put(b)\n")),
        ],
        &[
            ("words", &format!("fn f(a: [i64]) -> i64:\n    at(a)\n{late}")),
            ("literal", &format!("fn f() -> i64:\n    at([1, 2])\n{late}")),
            ("same", &format!("fn f(b: [u8]) -> i64:\n    first(b)\n\nfn first(data: Option<[u8]>) -> i64:\n    0\n")),
            ("method words", &format!("{bx}fn f(g: Box, a: [i64]) -> i64:\n    g.at(a)\n")),
            ("trait words", &format!("{tr}fn f(s: Store, a: [i64]) -> i64:\n    s.keep_words(a)\n")),
        ],
    );
}

/// Residual (3) of u8_array_into_word_array_residual_shapes_2026-11-28: a
/// trait-typed receiver that is not a bare local (`self.store.put(b)`, and
/// a nested field chain `self.inner.store.put(b)`). `trait_method_param_rows`
/// resolved `HirExprKind::Local` receivers only; a field receiver is a HIR
/// `FieldAccess` and the trait row was never consulted.
#[test]
fn u8_array_rejected_in_trait_method_on_field_receiver() {
    let tr = "trait Store:\n    fn keep_words(data: [i64]) -> i64\n    fn put(data: [i64]) -> i64\n\n";
    let cl = "class Widget:\n    val store: Store\n    fn direct(b: [u8]) -> i64:\n        return self.store.keep_words(b)\n    fn direct_builtin(b: [u8]) -> i64:\n        return self.store.put(b)\n\n";
    let nested = "class Holder:\n    val store: Store\n\nclass Outer:\n    val inner: Holder\n    fn nested(b: [u8]) -> i64:\n        return self.inner.store.keep_words(b)\n    fn nested_builtin(b: [u8]) -> i64:\n        return self.inner.store.put(b)\n\n";
    assert_u8_word_slot_cases(
        &[
            ("field receiver", &format!("{tr}{cl}")),
            ("field builtin name", &format!("{tr}{cl}").replace("self.store.keep_words(b)", "self.store.put(b)")),
            ("nested field receiver", &format!("{tr}{nested}")),
            ("nested field builtin name", &format!("{tr}{nested}").replace("self.inner.store.keep_words(b)", "self.inner.store.put(b)")),
        ],
        &[
            ("field words", &format!("{tr}{cl}").replace("b: [u8]", "b: [i64]")),
            ("nested words", &format!("{tr}{nested}").replace("b: [u8]", "b: [i64]")),
        ],
    );
}

/// Residual (4) of u8_array_into_word_array_residual_shapes_2026-11-28: a
/// `[u8]` pushed into a `[[i64]]` (or deeper) with the builtin
/// `push`/`append`. The builtin method path checked trait rows only; the
/// receiver's own element type was never compared with the pushed value.
#[test]
fn u8_array_rejected_in_builtin_push_word_element() {
    assert_u8_word_slot_cases(
        &[
            ("push", "fn f(b: [u8]) -> i64:\n    var rows: [[i64]] = []\n    rows.push(b)\n    0\n"),
            ("append", "fn f(b: [u8]) -> i64:\n    var rows: List<[i64]> = []\n    rows.append(b)\n    0\n"),
            ("deeper", "fn f(bb: [[u8]]) -> i64:\n    var rows: [[[i64]]] = []\n    rows.push(bb)\n    0\n"),
            ("var push", "fn f(b: [u8]) -> i64:\n    var rows: [[i64]] = []\n    rows.push(b)\n    rows[0][0]\n"),
        ],
        &[
            ("u8 rows", "fn f(b: [u8]) -> i64:\n    var rows: [[u8]] = []\n    rows.push(b)\n    0\n"),
            ("word rows", "fn f(a: [i64]) -> i64:\n    var rows: [[i64]] = []\n    rows.push(a)\n    0\n"),
            ("scalar", "fn f() -> i64:\n    var words: [i64] = []\n    words.push(7)\n    0\n"),
            ("untyped empty", "fn f(b: [u8]) -> i64:\n    var rows = []\n    rows.push(b)\n    0\n"),
            ("literal rows", "fn f() -> i64:\n    var rows: [[i64]] = []\n    rows.push([1, 2])\n    0\n"),
        ],
    );
}

/// Residual (5) of u8_array_into_word_array_residual_shapes_2026-11-28, NOT
/// fixed here: an untyped `list` relay erases the element type to ANY, so
/// the `[u8]` is invisible at the word slot. Pinned as admitted until a
/// provenance design lands; the runtime word-write trap still catches
/// writes, reads stay the risk.
#[test]
fn u8_array_through_untyped_list_relay_still_admitted() {
    let src = "fn relay(x: list) -> list:\n    return x\n\nfn take(w: [i64]) -> i64:\n    w[0]\n\nfn f(b: [u8]) -> i64:\n    take(relay(b))\n";
    parse_and_lower(src).unwrap_or_else(|e| panic!("untyped list relay must still lower (documented gap): {e:?}"));
}
