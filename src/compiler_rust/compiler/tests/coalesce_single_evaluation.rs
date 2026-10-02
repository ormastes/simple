//! Bootstrap lowering regression: calls must not be cloned into the present arm.
use simple_compiler::{hir, mir};
use simple_parser::Parser;

#[test]
fn coalesce_subject_calls_are_emitted_once_in_mir() {
    let source = r#"
fn subject() -> text?: "present"
fn other() -> text?: nil
fn fallback() -> text: "fallback"
fn direct() -> text: subject() ?? fallback()
fn nested() -> text: subject() ?? (other() ?? fallback())
fn scalar_subject() -> i64?: 42
fn scalar() -> i64: (scalar_subject() ?? 9) + 1
"#;
    let ast = Parser::new(source).parse().expect("coalesce fixture grammar");
    let hir = hir::lower(&ast).expect("coalesce HIR");
    let mir = mir::lower_to_mir(&hir).expect("coalesce MIR");
    for (function_name, callees) in [
        ("direct", vec!["subject", "fallback"]),
        ("nested", vec!["subject", "other", "fallback"]),
        ("scalar", vec!["scalar_subject"]),
    ] {
        let function = mir.functions.iter().find(|f| f.name == function_name).unwrap();
        for callee in callees {
            let count = function.blocks.iter().flat_map(|b| &b.instructions)
                .filter(|instruction| matches!(instruction,
                    mir::MirInst::Call { target, .. } if target.name() == callee))
                .count();
            assert_eq!(count, 1, "{function_name}: {callee} must have one call site");
        }
    }
}

#[test]
fn counter_fixture_lowers_through_bootstrap_hir_and_mir() {
    let source = include_str!("../../../../test/fixtures/compiler/coalesce_single_evaluation.spl");
    let ast = Parser::new(source).parse().expect("counter fixture grammar");
    let hir = hir::lower(&ast).expect("counter fixture HIR");
    mir::lower_to_mir(&hir).expect("counter fixture MIR");
}

#[test]
fn coalesce_counter_fixture_executes_once_with_lazy_defaults_in_jit() {
    use simple_compiler::codegen::JitCompiler;

    let source = include_str!("../../../../test/fixtures/compiler/coalesce_single_evaluation.spl");
    let ast = Parser::new(source).parse().expect("counter fixture grammar");
    let hir = hir::lower(&ast).expect("counter fixture HIR");
    let mir = mir::lower_to_mir(&hir).expect("counter fixture MIR");
    let mut jit = JitCompiler::new_static().expect("bootstrap Cranelift JIT");
    jit.compile_module(&mir).expect("counter fixture code generation");
    let result = unsafe { jit.call_i64_void("main").expect("counter fixture execution") };
    assert_eq!(result, 0, "coalesce semantic counter failed at fixture case {result}");
}
