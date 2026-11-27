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
