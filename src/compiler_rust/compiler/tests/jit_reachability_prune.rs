//! `mir::retain_reachable_functions` (used by `run_file_jit`) drops MIR
//! functions no root reaches. These tests pin that a pruned module still
//! JIT-compiles and runs, and that a MISSED edge would fail closed at JIT
//! compile time (the driver then falls back to the interpreter) rather than
//! finalising a call to a missing function.
//! doc/08_tracking/bug/jit_caret_392_unregistered_externs_hybrid_splice_2026-11-13.md

use std::collections::HashSet;
use std::fs;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};

const SOURCE: &str = "trait Shape:\n    fn area() -> i64\n\n\
class Sq with Shape:\n    s: i64\n    fn area() -> i64:\n        self.s * self.s\n\n\
class Rect with Shape:\n    w: i64\n    fn area() -> i64:\n        self.w\n\n\
class Holder:\n    sh: Shape\n\n\
fn measure(h: Holder) -> i64:\n    val x: Shape = h.sh\n    x.area()\n\n\
fn helper(x: i64) -> i64:\n    x + 1\n\n\
fn dead_one(x: i64) -> i64:\n    x * 1000\n\n\
fn dead_two(x: i64) -> i64:\n    dead_one(x) + 1\n\n\
fn main() -> i64:\n    measure(Holder(sh: Sq(s: 3))) * 100 + measure(Holder(sh: Rect(w: 2))) * 10 + helper(0)\n";

fn lower() -> mir::MirModule {
    let dir = tempfile::tempdir().expect("tempdir");
    let main = dir.path().join("main.spl");
    fs::write(&main, SOURCE).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main, &mut HashSet::new()).expect("flatten");
    let hir_module = hir::lower(&module).expect("HIR");
    mir::lower_to_mir(&hir_module).expect("MIR")
}

fn compile_and_run(module: &mir::MirModule) -> Result<i64, String> {
    let mut jit = JitCompiler::new_static().map_err(|e| format!("JIT: {e}"))?;
    jit.compile_module(module).map_err(|e| format!("JIT compile: {e}"))?;
    unsafe { jit.call_i64_void("main").map_err(|e| format!("run: {e}")) }
}

fn names(module: &mir::MirModule) -> Vec<String> {
    module.functions.iter().map(|f| f.name.clone()).collect()
}

#[test]
fn pruned_module_drops_dead_functions_and_runs_the_same() {
    let full = lower();
    let expected = compile_and_run(&full);
    assert_eq!(expected, Ok(9 * 100 + 2 * 10 + 1));

    let mut pruned = full.clone();
    let (before, after) = mir::retain_reachable_functions(&mut pruned);
    assert!(after < before, "nothing pruned: {:?}", names(&pruned));
    let kept = names(&pruned);
    for dead in ["dead_one", "dead_two"] {
        assert!(!kept.iter().any(|n| n == dead), "{dead} kept: {kept:?}");
    }
    for live in ["main", "measure", "helper"] {
        assert!(kept.iter().any(|n| n == live), "{live} dropped: {kept:?}");
    }
    assert!(
        kept.iter().filter(|n| n.ends_with("area")).count() >= 2,
        "vtable slot methods dropped: {kept:?}"
    );
    assert_eq!(compile_and_run(&pruned), expected);
}

/// Safety net: if reachability ever missed a direct-call edge, the call
/// becomes an undefined import and the JIT refuses the module (the driver
/// falls back to the interpreter) instead of jumping to NULL.
#[test]
fn a_missed_call_edge_fails_closed_at_jit_compile() {
    let mut module = lower();
    mir::retain_reachable_functions(&mut module);
    module.functions.retain(|f| f.name != "helper");
    let result = compile_and_run(&module);
    let err = result.expect_err("a call to a removed function must not compile");
    assert!(err.contains("helper"), "{err}");
}
