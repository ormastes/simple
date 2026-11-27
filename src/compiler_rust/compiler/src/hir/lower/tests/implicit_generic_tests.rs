//! Stage 1 implicit generics: an unannotated parameter is a type variable
//! instantiated per call site, never `any`.
//! doc/08_tracking/bug/seed_value_join_any_option_disagree_wrong_values_2026-11-27.md

use crate::hir::lower::{LowerResult, Lowerer};
use crate::hir::types::{HirExprKind, HirModule, HirStmt, HirType, TypeId};
use simple_parser::Parser;

/// The run/JIT lane's lowering mode (unannotated parameters are accepted).
fn lower_run_lane(source: &str) -> LowerResult<HirModule> {
    let module = Parser::new(source).parse().expect("parse failed");
    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    lowerer.lower_module(&module)
}

fn local_ty(module: &HirModule, function: &str, local: &str) -> TypeId {
    let function = module.functions.iter().find(|f| f.name == function).unwrap();
    function.locals.iter().find(|l| l.name == local).unwrap().ty
}

fn is_f64_array(module: &HirModule, ty: TypeId) -> bool {
    matches!(module.types.get(ty), Some(HirType::Array { element, .. }) if *element == TypeId::F64)
}

const UNTYPED: &str = "fn untyped(x):\n    x\n";
const GENERIC: &str = "fn untyped<T>(x: T) -> T:\n    x\n";
const RETURNING: &str = "fn untyped(x):\n    return x\n";

#[test]
fn unannotated_identity_is_instantiated_per_call_site() {
    for decl in [UNTYPED, GENERIC, RETURNING] {
        let source = format!(
            "{decl}fn probe(xs: [f64], n: i64, s: text) -> f64:\n    val r = untyped(xs)\n    val k = untyped(n)\n    val t = untyped(s)\n    r[0] + 0.25\n"
        );
        let module = lower_run_lane(&source).unwrap();
        assert!(is_f64_array(&module, local_ty(&module, "probe", "r")), "{decl}: r must be [f64]");
        assert_eq!(local_ty(&module, "probe", "k"), TypeId::I64, "{decl}");
        assert_eq!(local_ty(&module, "probe", "t"), TypeId::STRING, "{decl}");
    }
}

#[test]
fn numeric_instantiation_decodes_the_erased_result_with_a_cast() {
    let source = format!("{UNTYPED}fn probe(n: f64) -> f64:\n    val k = untyped(n)\n    k + 0.25\n");
    let module = lower_run_lane(&source).unwrap();
    let probe = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let HirStmt::Let { value: Some(value), .. } = &probe.body[0] else { panic!("expected initializer") };
    let HirExprKind::Cast { expr, target } = &value.kind else { panic!("expected a decoding cast, got {:?}", value.kind) };
    assert_eq!(*target, TypeId::F64);
    assert_eq!(expr.ty, TypeId::ANY, "the callee itself still returns the erased word");
    assert!(matches!(expr.kind, HirExprKind::Call { .. }));
}

#[test]
fn join_of_empty_array_and_unannotated_identity_is_the_instantiated_array() {
    for (decl, expression) in [
        (UNTYPED, "if c: [] else: untyped(xs)"),
        (UNTYPED, "if c: untyped(xs) else: []"),
        (GENERIC, "if c: [] else: untyped(xs)"),
    ] {
        let source = format!(
            "{decl}fn probe(xs: [f64], c: bool) -> f64:\n    val r = {expression}\n    if r.len() > 0: r[0] + 0.25 else: -2.0\n"
        );
        let module = lower_run_lane(&source).unwrap();
        assert!(is_f64_array(&module, local_ty(&module, "probe", "r")), "{expression}");
    }
}

#[test]
fn match_join_with_unannotated_identity_is_the_instantiated_array() {
    let source = format!(
        "enum K:\n    A\n    B\n{UNTYPED}fn probe(xs: [f64], k: K) -> f64:\n    val r = match k:\n        case K.A: []\n        case _: untyped(xs)\n    if r.len() > 0: r[0] + 0.25 else: -2.0\n"
    );
    let module = lower_run_lane(&source).unwrap();
    assert!(is_f64_array(&module, local_ty(&module, "probe", "r")));
}

fn rejected(source: &str) -> String {
    let error = lower_run_lane(source).expect_err("an uninferred typed use must be rejected");
    let text = format!("{error}");
    assert!(text.contains("SIMPLE_JIT_STRICT:"), "must not be demotable to the interpreter: {text}");
    assert!(text.contains("cannot infer a type"), "{text}");
    text
}

#[test]
fn uninferred_result_is_rejected_at_typed_uses() {
    // `opaque` is not the identity shape, so stage 1 cannot instantiate it.
    let opaque = "fn opaque(x):\n    val y = x\n    y\n";
    let index = format!("{opaque}fn probe(xs: [f64]) -> f64:\n    val r = opaque(xs)\n    r[0]\n");
    assert!(rejected(&index).contains("`opaque`"));
    let arithmetic = format!("{opaque}fn probe(n: f64) -> f64:\n    opaque(n) + 0.25\n");
    assert!(rejected(&arithmetic).contains("arithmetic"));
    let join = format!("{opaque}fn probe(xs: [f64], c: bool) -> i64:\n    val r = if c: xs else: opaque(xs)\n    r.len()\n");
    assert!(rejected(&join).contains("joined with a typed arm"));
    // An empty literal instantiates nothing: no `[any]`.
    let empty = format!("{UNTYPED}fn probe() -> f64:\n    val r = untyped([])\n    r[0]\n");
    rejected(&empty);
}

#[test]
fn unannotated_parameter_is_rejected_in_arithmetic() {
    let text = rejected("fn add(a, b):\n    a + b\nfn probe() -> i64:\n    0\n");
    assert!(text.contains("unannotated parameter `a` of `add`"), "{text}");
}

#[test]
fn unsafe_and_annotated_uses_stay_permitted() {
    let opaque = "fn opaque(x):\n    val y = x\n    y\n";
    let in_unsafe = format!("{opaque}fn probe(n: f64) -> f64:\n    unsafe:\n        return opaque(n) + 0.25\n    0.0\n");
    lower_run_lane(&in_unsafe).expect("`any` arithmetic is permitted inside unsafe");
    let annotated = format!("{opaque}fn probe(xs: [f64]) -> f64:\n    val r: [f64] = opaque(xs)\n    r[0]\n");
    lower_run_lane(&annotated).expect("an annotated binding is typed");
    let passthrough = format!("{opaque}fn probe(xs: [f64]) -> i64:\n    val r = opaque(xs)\n    print(r)\n    0\n");
    lower_run_lane(&passthrough).expect("an uninferred value may be passed on untouched");
}

#[test]
fn script_entry_keeps_dynamic_typing() {
    let source = "fn add(a, b):\n    a + b\nval total = add(1, 2)\nprint(total + 1)\n";
    let module = Parser::new(source).parse().expect("parse failed");
    let wrapped = crate::pipeline::native_project::wrap_entry_script_as_main(module, false);
    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    lowerer.lower_module(&wrapped).expect("script mode permits `any`");
}

#[test]
fn unannotated_procedure_call_is_not_an_uninferred_value() {
    let die = "fn die(msg: text):\n    print(msg)\n";
    let probe = "enum K:\n    A\n    B\n    C\nfn probe(xs: [f64], k: K) -> i64:\n    val r = match k:\n        case K.A: xs\n        case K.B: die(\"died\")\n        case K.C: xs\n    r.len()\n";
    // Declared before and after its use: the verdict waits for the body.
    lower_run_lane(&format!("{die}{probe}")).expect("a procedure arm is `()`, not an uninferred value");
    lower_run_lane(&format!("{probe}{die}")).expect("a forward-referenced procedure arm is `()` too");
}

#[test]
fn forward_referenced_unannotated_function_is_still_rejected() {
    let source = "fn probe(xs: [f64]) -> f64:\n    val r = opaque(xs)\n    r[0]\nfn opaque(x):\n    val y = x\n    y\n";
    assert!(rejected(source).contains("`opaque`"));
}

#[test]
fn mainless_unit_with_top_level_statements_is_a_script() {
    let source = "fn add(a, b):\n    a + b\nprint(add(1, 2) + 1)\n";
    let module = Parser::new(source).parse().expect("parse failed");
    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    lowerer.set_mainless_unit_is_script(true);
    lowerer.lower_module(&module).expect("a script unit keeps dynamic typing on the run lane");
    // Per-module lanes: a module with a top-level statement is not a script.
    rejected(source);
    let module_with_main = "fn add(a, b):\n    a + b\nfn main():\n    print(add(1, 2))\n";
    rejected(module_with_main);
}

#[test]
fn forward_referenced_identity_is_instantiated_too() {
    let source = format!("fn probe(xs: [f64], n: f64) -> f64:\n    val r = untyped(xs)\n    val k = untyped(n)\n    r[0] + k\n{UNTYPED}");
    let module = lower_run_lane(&source).unwrap();
    assert!(is_f64_array(&module, local_ty(&module, "probe", "r")));
    assert_eq!(local_ty(&module, "probe", "k"), TypeId::F64);
}

#[test]
fn one_type_variable_is_not_instantiated_from_disagreeing_arguments() {
    let pick = "fn pick<T>(a: T, b: T) -> T:\n    a\n";
    let agree = format!("{pick}fn probe(x: f64, y: f64) -> f64:\n    val r = pick(x, y)\n    r\n");
    assert_eq!(local_ty(&lower_run_lane(&agree).unwrap(), "probe", "r"), TypeId::F64);
    let disagree = format!("{pick}fn probe(x: f64) -> f64:\n    val r = pick(0, x)\n    r\n");
    assert_eq!(local_ty(&lower_run_lane(&disagree).unwrap(), "probe", "r"), TypeId::ANY);
}

#[test]
fn shadowing_local_is_not_rejected_for_an_earlier_uninferred_name() {
    let source = "fn opaque(x):\n    val y = x\n    y\nfn probe(xs: [f64]) -> f64:\n    val r = opaque(xs)\n    print(r)\n    val r = xs\n    r[0] + 0.25\n";
    lower_run_lane(source).expect("the second `r` is `[f64]`");
}
