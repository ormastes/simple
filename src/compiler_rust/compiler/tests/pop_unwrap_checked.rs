//! `.unwrap()` on an optional array accessor (`pop`/`first`/`last`/`remove`)
//! must lower to the CHECKED unwrap typed as the element, not to dynamic
//! dispatch typed ANY. Pairs with the pure-Simple MIR spec
//! `test/01_unit/compiler/mir/pop_unwrap_checked_lowering_spec.spl`.
//! Regression: doc/08_tracking/bug/stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn lower(source: &str) -> mir::MirModule {
    let ast = Parser::new(source).parse().expect("fixture grammar");
    let hir = hir::lower(&ast).expect("fixture HIR");
    mir::lower_to_mir(&hir).expect("fixture MIR")
}

fn call_count(function: &mir::MirFunction, callee: &str) -> usize {
    function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|instruction| {
            matches!(instruction, mir::MirInst::Call { target, .. } if target.name() == callee)
        })
        .count()
}

#[test]
fn accessor_unwrap_lowers_to_checked_unwrap_in_mir() {
    let source = r#"
fn pop_scalar() -> i64:
    var xs = [1, 2]
    xs.pop().unwrap()
fn first_scalar() -> i64:
    val xs = [1, 2]
    xs.first().unwrap()
fn last_scalar() -> i64:
    val xs = [1, 2]
    xs.last().unwrap()
fn remove_scalar() -> i64:
    var xs = [1, 2]
    xs.remove(0).unwrap()
fn pop_tuple() -> i64:
    var xs = [(1, true), (2, false)]
    val (n, f) = xs.pop().unwrap()
    n
"#;
    let module = lower(source);
    for name in ["pop_scalar", "first_scalar", "last_scalar", "remove_scalar", "pop_tuple"] {
        let function = module.functions.iter().find(|f| f.name == name).unwrap();
        let debug = format!("{function:?}");
        assert_eq!(
            call_count(function, "rt_unwrap_or_trap"),
            1,
            "{name}: the checked unwrap helper must be called exactly once:\n{debug}"
        );
        assert!(
            !debug.contains("\"unwrap\""),
            "{name}: `.unwrap()` must not remain a dynamic method dispatch:\n{debug}"
        );
    }
}

#[test]
fn accessor_unwrap_and_coalesce_evaluate_the_accessor_once() {
    let source = r#"
fn make() -> [i64]:
    [1, 2]
fn via_unwrap() -> i64:
    make().pop().unwrap()
fn via_coalesce() -> i64:
    make().pop() ?? -1
"#;
    let module = lower(source);
    for name in ["via_unwrap", "via_coalesce"] {
        let function = module.functions.iter().find(|f| f.name == name).unwrap();
        assert_eq!(call_count(function, "make"), 1, "{name}: receiver producer called once");
    }
}

#[test]
fn pop_unwrap_fixture_executes_in_jit() {
    use simple_compiler::codegen::JitCompiler;

    let source = include_str!("../../../../test/fixtures/compiler/pop_unwrap_checked.spl");
    let module = lower(source);
    let mut jit = JitCompiler::new_static().expect("bootstrap Cranelift JIT");
    jit.compile_module(&module).expect("fixture code generation");
    let result = unsafe { jit.call_i64_void("main").expect("fixture execution") };
    assert_eq!(result, 0, "pop/unwrap/coalesce fixture failed at case {result}");
}
