//! A trait-typed value read from a FIELD into a local must dispatch through the
//! trait vtable under the JIT, also when the function lives in an imported
//! (flattened) module, and a receiver that carries no vtable must fail with a
//! clean runtime error instead of SIGSEGV.
//!
//! Live shape: `_pure_database_select_owned_v1` in
//! `src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl`
//! (`val strategy = slot.reducer; strategy.provider_identity()`), the first
//! whole-module JIT fallback of `src/app/llm_caret/main.spl`. Two classes in the
//! unit share the method name, so a bare-name call is refused as
//! `[CODEGEN-AMBIGUOUS-METHOD]` and the whole module drops to the interpreter.
//! Design: doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md
//! Bug (structural conformer): doc/08_tracking/bug/jit_vtable_call_on_structural_conformer_sigsegv_2026-11-13.md

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};

fn write(root: &Path, rel: &str, body: &str) {
    let path = root.join(rel);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, body).unwrap();
}

const REDUCER: &str = "trait Reducer:\n    fn bits() -> i64\n    fn tag() -> i64\n\nclass Slot:\n    r: Reducer\n\n\
pub fn annotated_bits(slot: Slot?) -> i64:\n    if val Some(s) = slot:\n        val x: Reducer = s.r\n        return x.bits()\n    -1\n\n\
pub fn field_local_bits(slot: Slot?) -> i64:\n    if val Some(s) = slot:\n        val x = s.r\n        return x.bits()\n    -1\n";

/// Two unrelated classes declaring `bits`, so a bare-name `bits` is ambiguous.
const AB: &str = "class A:\n    n: i64\n    fn bits() -> i64:\n        self.n\n\n\
class B:\n    n: i64\n    fn bits() -> i64:\n        self.n + 1\n\n\
pub fn ab_sum() -> i64:\n    A(n: 1).bits() + B(n: 1).bits()\n";

const NOMINAL: &str = "use db.reducer.{Reducer}\n\nclass C with Reducer:\n    n: i64\n    fn bits() -> i64:\n        self.n\n    fn tag() -> i64:\n        1\n";

/// Same method set as `Reducer`, but no `with Reducer`: no vtable header.
const STRUCTURAL: &str = "class D:\n    n: i64\n    fn bits() -> i64:\n        self.n\n    fn tag() -> i64:\n        2\n";

/// Flatten `main_body` (plus the fixed modules) through the real loader, lower,
/// JIT-compile and run `main`.
fn compile_and_run(main_body: &str) -> Result<i64, String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    write(&src, "db/reducer.spl", REDUCER);
    write(&src, "other/ab.spl", AB);
    write(&src, "impls/c.spl", NOMINAL);
    write(&src, "impls/d.spl", STRUCTURAL);
    let main = src.join("main.spl");
    fs::write(&main, main_body).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main, &mut HashSet::new())
        .map_err(|e| format!("flatten: {e}"))?;
    let hir_module = hir::lower(&module).map_err(|e| format!("HIR: {e}"))?;
    let mir_module = mir::lower_to_mir(&hir_module).map_err(|e| format!("MIR: {e}"))?;
    let full = run_main(&mir_module);
    // `run_file_jit` prunes unreachable functions first; the dispatch
    // decisions (vtable, by-name bind, ambiguity) must not change with it.
    let mut pruned = mir_module;
    mir::retain_reachable_functions(&mut pruned);
    assert_eq!(run_main(&pruned), full, "reachability pruning changed the result");
    full
}

fn run_main(mir_module: &mir::MirModule) -> Result<i64, String> {
    let mut jit = JitCompiler::new_static().map_err(|e| format!("JIT: {e}"))?;
    jit.compile_module(mir_module).map_err(|e| format!("JIT compile: {e}"))?;
    unsafe { jit.call_i64_void("main").map_err(|e| format!("run: {e}")) }
}

const IMPORTS: &str = "use db.reducer.{Slot, annotated_bits, field_local_bits}\nuse other.ab.{ab_sum}\n";

#[test]
fn nominal_conformer_dispatches_through_vtable_from_flattened_free_function() {
    let main = format!(
        "{IMPORTS}use impls.c.{{C}}\n\nfn main() -> i64:\n    val s = Slot(r: C(n: 7))\n    \
         annotated_bits(Some(s)) * 100 + field_local_bits(Some(s)) * 10 + ab_sum() - 3\n"
    );
    assert_eq!(compile_and_run(&main), Ok(770));
}

#[test]
fn zero_conformers_still_compile_and_the_call_is_never_reached() {
    let main = format!(
        "{IMPORTS}\nfn main() -> i64:\n    annotated_bits(nil) * 100 + field_local_bits(nil) * 10 + ab_sum()\n"
    );
    assert_eq!(compile_and_run(&main), Ok(-100 - 10 + 3));
}

/// Only a structural conformer in the unit (no implementor carries a vtable):
/// the call keeps the by-name bind to that one class and returns its value.
#[test]
fn sole_structural_conformer_keeps_the_by_name_bind() {
    let main = format!(
        "{IMPORTS}use impls.d.{{D}}\n\nfn main() -> i64:\n    val s = Slot(r: D(n: 9))\n    \
         annotated_bits(Some(s)) * 100 + field_local_bits(Some(s)) * 10 + ab_sum() - 3\n"
    );
    assert_eq!(compile_and_run(&main), Ok(990));
}

const CHILD_ENV: &str = "SIMPLE_TEST_JIT_STRUCTURAL_CONFORMER_CHILD";

/// Child half of `structural_conformer_fails_cleanly_not_sigsegv`; a no-op
/// unless spawned by it, because the expected outcome ends the process.
/// The trait IS implemented (`C`), so the call is a vtable call, and a `D`
/// (no `with`, no vtable word) reaches it.
#[test]
fn structural_conformer_child() {
    if std::env::var_os(CHILD_ENV).is_none() {
        return;
    }
    let main = format!(
        "{IMPORTS}use impls.c.{{C}}\nuse impls.d.{{D}}\n\nfn main() -> i64:\n    val c = Slot(r: C(n: 7))\n    \
         val s = Slot(r: D(n: 9))\n    annotated_bits(Some(c)) + annotated_bits(Some(s)) + ab_sum()\n"
    );
    let result = compile_and_run(&main);
    println!("child-result={result:?}");
}

#[test]
fn structural_conformer_fails_cleanly_not_sigsegv() {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["structural_conformer_child", "--exact", "--nocapture", "--test-threads=1"])
        .env(CHILD_ENV, "1")
        .output()
        .expect("spawn child test");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(output.status.signal(), None, "child died by signal; stdout={stdout} stderr={stderr}");
    }
    assert_eq!(
        output.status.code(),
        Some(70),
        "expected rt_method_not_found exit 70; stdout={stdout} stderr={stderr}"
    );
    assert!(stderr.contains("not found"), "stderr must name the dispatch miss: {stderr}");
}
