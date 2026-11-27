//! parse_family_strips_option_jit_native_2026-08-02 (erased-boundary part):
//! a primitive `T?` such as `"12".parse_int()` is carried in its raw form (the
//! tagged payload, or nil). Passed to an untyped parameter, a statement
//! `match x: Some(v)` bound `v` through `rt_enum_payload`, which answers nil for
//! a non-enum, so `v` read nil where the interpreter binds 12.
use simple_parser::Parser;

fn jit_evaluate(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

/// Same, with the project-wide enum table the native-project lane supplies.
fn jit_evaluate_with_global_enums(
    source: &str,
    enums: &[(&str, Vec<(String, Option<Vec<simple_parser::Type>>)>)],
) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let defs = enums.iter().map(|(n, vs)| (n.to_string(), vs.clone())).collect();
    lowerer.set_global_enum_defs(std::sync::Arc::new(defs));
    lowerer.register_global_enums();
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

#[test]
fn jit_some_pattern_binds_raw_optional_through_untyped_parameter() {
    let source = "fn g(x) -> i64:\n    var r = -9\n    match x:\n        Some(v): r = v + 1000\n        None: r = -5\n    r\nfn main() -> i64:\n    val a = \"12\".parse_int()\n    val b = \"zz\".parse_int()\n    val c: i64? = Some(7)\n    g(a) * 1000000 + g(c) * 100 + g(b)\n";
    // g(a) = 1012, g(c) = 1007, g(b) = -5
    assert_eq!(jit_evaluate(source), 1_012_000_000 + 100_700 - 5);
}

/// A user enum with a variant named `Some` keeps the plain payload binding,
/// and its other variants do not take a bare `Some` arm.
/// seed_jit_any_match_bare_some_arm_takes_user_enum_unit_variant_2026-11-27
#[test]
fn jit_some_pattern_on_user_enum_through_untyped_parameter() {
    let source = "enum Opt:\n    Some(i64)\n    Nope\nfn g(x) -> i64:\n    var r = -9\n    match x:\n        Some(v): r = v\n        Nope: r = -5\n    r\nfn main() -> i64:\n    g(Opt.Some(4)) * 10 + g(Opt.Nope) * -1\n";
    assert_eq!(jit_evaluate(source), 45);
}

/// `if val Some(v) = x` and an expression `match` share the same binding.
#[test]
fn jit_if_val_and_match_expression_bind_raw_optional() {
    let source = "fn h(x) -> i64:\n    if val Some(v) = x:\n        return v + 1000\n    -5\nfn e(x) -> i64:\n    match x:\n        Some(v) => v + 2000\n        None => -6\nfn main() -> i64:\n    val a = \"12\".parse_int()\n    val b = \"zz\".parse_int()\n    h(a) * 1000000 + e(a) * 10 + h(b) + e(b)\n";
    // h(a) = 1012, e(a) = 2012, h(b) = -5, e(b) = -6
    assert_eq!(jit_evaluate(source), 1_012_000_000 + 20_120 - 11);
}

/// Raw `text?` and `bool?` payloads bind as themselves too.
#[test]
fn jit_some_pattern_binds_raw_text_and_bool_optionals() {
    let source = "fn tl(x) -> i64:\n    match x:\n        Some(v): return v.len()\n        None: return -5\n    -9\nfn bt(x) -> i64:\n    match x:\n        Some(v):\n            if v:\n                return 1\n            return 2\n        None: return -5\n    -9\nfn main() -> i64:\n    val t: text? = \"hey\"\n    val f: bool? = false\n    tl(t) * 10 + bt(f)\n";
    assert_eq!(jit_evaluate(source), 32);
}

/// A USER enum named `Option` is an ordinary enum object, so its `Some` arm
/// through an untyped parameter keeps the plain payload read.
/// seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16
#[test]
fn jit_user_enum_named_option_binds_payload_through_untyped_parameter() {
    let source = "enum Option:\n    Some(i64)\n    None\nfn g(x) -> i64:\n    match x:\n        Some(v): return v\n        None: return 99\n    -9\nfn main() -> i64:\n    g(Option::Some(42)) * 1000 + g(Option::None)\n";
    assert_eq!(jit_evaluate(source), 42_099);
}

/// A generic builtin `Option<T>` in the project-wide table (legacy std
/// core/option.spl) is not a user enum and must not disable the raw binding.
#[test]
fn jit_builtin_shaped_global_option_keeps_raw_binding() {
    let builtin_option = vec![
        (
            "Some".to_string(),
            Some(vec![simple_parser::Type::Simple("T".to_string())]),
        ),
        ("None".to_string(), None),
    ];
    let source = "fn g(x) -> i64:\n    match x:\n        Some(v): return v + 1000\n        None: return -5\n    -9\nfn main() -> i64:\n    g(\"12\".parse_int())\n";
    assert_eq!(
        jit_evaluate_with_global_enums(source, &[("Option", builtin_option)]),
        1012
    );
}

/// A program that declares a `Some`-owning enum still binds raw optionals and
/// other enums as themselves (the interpreter's flat-Option rule).
#[test]
fn jit_raw_optional_binds_with_some_owning_enum_declared() {
    let source = "enum Opt:\n    Some(i64)\n    Nope\nenum Col:\n    Red\n    Blue(i64)\nfn g(x) -> i64:\n    match x:\n        Some(v): return 1\n        None: return 2\n    3\nfn n(x) -> i64:\n    match x:\n        Some(v): return v + 1000\n        None: return -5\n    -9\nfn main() -> i64:\n    val a = \"12\".parse_int()\n    val b = \"zz\".parse_int()\n    n(a) * 1000 + n(b) * -1 + g(Col.Red) * 100\n";
    // n(a) = 1012, n(b) = -5, g(Col.Red) = 1
    assert_eq!(jit_evaluate(source), 1_012_000 + 5 + 100);
}

/// `if val Some(v)` and an expression `match` refuse `Opt.Nope` too.
#[test]
fn jit_if_val_and_match_expression_refuse_user_enum_unit_variant() {
    let source = "enum Opt:\n    Some(i64)\n    Nope\nfn h(x) -> i64:\n    if val Some(v) = x:\n        return v\n    -5\nfn e(x) -> i64:\n    match x:\n        Some(v) => v\n        _ => -6\nfn main() -> i64:\n    h(Opt.Nope) * 100 + e(Opt.Nope) * 10 + h(Opt.Some(4)) + e(Opt.Some(4))\n";
    assert_eq!(jit_evaluate(source), -500 - 60 + 8);
}

/// A generic Some-owner binds its own payload through an untyped parameter.
#[test]
fn jit_generic_some_owner_binds_payload_through_untyped_parameter() {
    let source = "enum Bi<T>:\n    Some(T)\n    None\nfn g(x) -> i64:\n    match x:\n        Some(v): return v\n        None: return -5\n    -9\nfn main() -> i64:\n    val b: Bi<i64> = Bi.Some(7)\n    g(b)\n";
    assert_eq!(jit_evaluate(source), 7);
}

/// An explicit `Some(0.1)` in an `f64?` slot is an Option enum whose payload
/// slot holds the raw IEEE-754 bits. Through an untyped parameter the binder
/// has no static type, so `v` read those bits as a tagged int
/// (`Some(1.5)` bound 576179277326712832). The `any` boundary now hands the
/// callee the raw `f64?` form (a tagged float), like `val b: f64? = 0.1`.
/// seed_jit_erased_f64_option_some_binds_raw_bits_2026-11-27
#[test]
fn jit_explicit_f64_option_some_binds_float_through_untyped_parameter() {
    let source = "fn h(x) -> i64:\n    match x:\n        Some(v):\n            if v == 0.1:\n                return 1\n            return 3\n        None: return 4\n    5\nfn add(x) -> f64:\n    match x:\n        Some(v): return v + 0.25\n        None: return -1.0\n    -2.0\nfn relay(x):\n    return x\nfn main() -> i64:\n    val a: f64? = Some(0.1)\n    val b: f64? = 0.1\n    val c: f64? = None\n    val d: f64? = Some(1.5)\n    val r: f64? = relay(a)\n    var back = 0\n    if (r ?? 9.0) == 0.1:\n        back = 1\n    var sum = 0\n    if add(d) == 1.75:\n        sum = 1\n    h(a) * 10000 + h(b) * 1000 + h(c) * 100 + back * 10 + sum\n";
    // h(a) = 1, h(b) = 1, h(c) = 4, relay round trip = 1, add(d) = 1.75
    assert_eq!(jit_evaluate(source), 11_411);
}

/// A bare `None` arm over an untyped subject matches a user enum's own `None`
/// variant (interpreter: any enum value whose variant is named `None`), for an
/// enum declaring `Some`/`None` and for a `None`-only enum, while nil and a
/// raw present value keep their meaning.
/// seed_jit_any_match_bare_none_arm_misses_user_enum_none_2026-11-27
#[test]
fn jit_bare_none_arm_matches_user_enum_none_through_untyped_parameter() {
    let source = "enum Opt:\n    Some(i64)\n    None\nenum Q:\n    Here(i64)\n    None\nfn g(x) -> i64:\n    match x:\n        Some(v): return v\n        None: return -5\n    -9\nfn q(x) -> i64:\n    match x:\n        None: return -6\n        Here(v): return v\n    -9\nfn e(x) -> i64:\n    match x:\n        None => 1\n        _ => 2\nfn main() -> i64:\n    val z: i64? = None\n    val p = \"12\".parse_int()\n    g(Opt.Some(4)) * 1000000 + g(Opt.None) * -100000 + g(z) * -10000 + q(Q.None) * -1000 + q(Q.Here(3)) * 100 + e(Opt.None) * 10 + e(p)\n";
    // g: 4, -5, -5; q: -6, 3; e(Opt.None) = 1, e(raw 12) = 2
    assert_eq!(
        jit_evaluate(source),
        4_000_000 + 500_000 + 50_000 + 6_000 + 300 + 10 + 2
    );
}

/// `case nil:` agrees with `case None:` over an untyped subject (interpreter:
/// nil literal pattern also matches an enum value whose variant is `None`).
#[test]
fn jit_nil_arm_matches_user_enum_none_through_untyped_parameter() {
    let source = "enum Opt:\n    Some(i64)\n    None\nfn g(x) -> i64:\n    match x:\n        nil: return -5\n        _: return 1\n    -9\nfn e(x) -> i64:\n    match x:\n        nil => 3\n        _ => 4\nfn main() -> i64:\n    val z: i64? = None\n    g(Opt.None) * -1000 + g(Opt.Some(2)) * 100 + g(z) * -10 + e(Opt.None)\n";
    assert_eq!(jit_evaluate(source), 5_000 + 100 + 50 + 3);
}

/// The `Option<f64>` spelling takes the same boundary as `f64?`.
#[test]
fn jit_explicit_option_f64_some_binds_float_through_untyped_parameter() {
    let source = "fn h(x) -> i64:\n    match x:\n        Some(v):\n            if v == 0.5:\n                return 1\n            return 3\n        None: return 4\n    5\nfn main() -> i64:\n    val o: Option<f64> = Some(0.5)\n    val n: Option<f64> = None\n    h(o) * 10 + h(n)\n";
    assert_eq!(jit_evaluate(source), 14);
}

/// The boundary's temporary slot must not alias a caller parameter.
#[test]
fn jit_f64_option_boundary_in_caller_with_parameters() {
    let source = "fn h(x) -> i64:\n    match x:\n        Some(v):\n            if v == 0.1:\n                return 1\n            return 3\n        None: return 4\n    5\nfn wrap(a: f64?, n: i64, z: f64?) -> i64:\n    val t = n * 2\n    h(a) * 100 + h(z) * 10 + t\nfn main() -> i64:\n    wrap(Some(0.1), 3, None)\n";
    assert_eq!(jit_evaluate(source), 146);
}

/// A direct `Some(<f64>)` argument (HIR types the call ANY) crosses too.
#[test]
fn jit_direct_f64_some_literal_binds_float_through_untyped_parameter() {
    let source = "fn h(x) -> i64:\n    match x:\n        Some(v):\n            if v == 0.1:\n                return 1\n            return 3\n        None: return 4\n    5\nfn main() -> i64:\n    h(Some(0.1))\n";
    assert_eq!(jit_evaluate(source), 1);
}

/// Builtin `Result` values (runtime id 0) never take a bare `None` / `nil`
/// arm, beside a `Some|None` enum and a None-first enum
/// (`rt_enum_check_variant` treats an actual id 0 as a wildcard).
#[test]
fn jit_bare_none_arm_refuses_result_values_through_untyped_parameter() {
    let source = "enum Opt:\n    Some(i64)\n    None\nenum Q:\n    None\n    Here(i64)\nfn g(x) -> i64:\n    match x:\n        None: return -5\n        _: return 7\n    -9\nfn n(x) -> i64:\n    match x:\n        nil: return -5\n        _: return 7\n    -9\nfn e(x) -> i64:\n    match x:\n        None => 1\n        _ => 2\nfn main() -> i64:\n    val ok: Result<i64, text> = Ok(3)\n    val er: Result<i64, text> = Err(\"e\")\n    g(ok) * 100000 + g(er) * 10000 + n(ok) * 1000 + n(er) * 100 + e(ok) * 10 + e(er) - g(Q.None) * 1000000 - g(Opt.None) * 10000000\n";
    // Result values: 7 7 7 7 2 2; Q.None and Opt.None: -5
    assert_eq!(
        jit_evaluate(source),
        700_000 + 70_000 + 7_000 + 700 + 20 + 2 + 5_000_000 + 50_000_000
    );
}

/// Owners whose `None` shares a discriminant (None-first enums) are told
/// apart by identity: `Q2.Here` and `Col.Red` (discriminant 0, not owners of
/// that variant) never match, both `None`s do, on the first and later calls.
#[test]
fn jit_bare_none_arm_with_shared_owner_discriminants() {
    let source = "enum Q1:\n    None\n    A(i64)\nenum Q2:\n    None\n    B(i64)\nenum Col:\n    Red\n    Blue\nfn g(x) -> i64:\n    match x:\n        None: return 1\n        _: return 0\n    -9\nfn main() -> i64:\n    var s = 0\n    var i = 0\n    while i < 3:\n        s = s * 10000 + g(Q1.None) * 1000 + g(Q2.None) * 100 + g(Col.Red) * 10 + g(Q2.B(4))\n        i = i + 1\n    s\n";
    assert_eq!(jit_evaluate(source), 110_011_001_100);
}

/// The match is by the value's own variant name, wherever the value came
/// from: stored in an untyped list, returned from a function, carrying a
/// payload, or built in a loop. `Q.Here` beside it never matches.
#[test]
fn jit_bare_none_arm_matches_user_none_after_list_and_return_round_trips() {
    let source = "enum Q:\n    None\n    Here(i64)\nenum P:\n    Full(i64)\n    None(i64)\nfn g(x) -> i64:\n    match x:\n        None: return 1\n        _: return 0\n    -9\nfn mk() -> Q:\n    Q.None\nfn mkh() -> Q:\n    Q.Here(3)\nfn main() -> i64:\n    var xs = []\n    xs.push(Q.None)\n    xs.push(Q.Here(1))\n    var s = g(xs[0]) * 100000 + g(xs[1]) * 10000 + g(mk()) * 1000 + g(mkh()) * 100 + g(P.None(4)) * 10 + g(P.Full(4))\n    var i = 0\n    while i < 3:\n        s = s + g(Q.None) * 1000000\n        i = i + 1\n    s\n";
    assert_eq!(jit_evaluate(source), 3_101_010);
}

/// A typed `Q?` holding `Q.None` is present: `rt_is_none` (the typed-optional
/// test) ignores the stamp a bare erased `None` arm reads.
#[test]
fn jit_typed_optional_holding_user_none_stays_present() {
    let source = "enum Q:\n    None\n    Here(i64)\nfn t(x: Q?) -> i64:\n    if x.?:\n        return 1\n    0\nfn g(x) -> i64:\n    match x:\n        None: return 1\n        _: return 0\n    -9\nfn main() -> i64:\n    val a: Q? = Q.None\n    val b: Q? = nil\n    t(a) * 10000 + t(b) * 1000 + g(Q.None)\n";
    assert_eq!(jit_evaluate(source), 10_001);
}
