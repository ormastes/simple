//! A bare call of a name the calling module both declares and selectively
//! imports is chosen by its arguments; a tie is a compile error; a module's
//! own function beats a same-named spec-DSL word.
//! Bug: doc/08_tracking/bug/seed_same_name_fn_binding_2026-11-27.md.

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

fn lower(files: &[(&str, &str)], main: &str) -> Result<mir::MirModule, String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    for (rel, body) in files {
        write(&src, rel, body);
    }
    let main_path = src.join("main.spl");
    fs::write(&main_path, main).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .expect("flatten");
    let hir_module = hir::lower(&module).map_err(|e| e.to_string())?;
    mir::lower_to_mir(&hir_module).map_err(|e| e.to_string())
}

fn run_main(mir_module: &mir::MirModule) -> i64 {
    let mut jit = JitCompiler::new_static().expect("JIT");
    jit.compile_module(mir_module).expect("JIT compile");
    unsafe { jit.call_i64_void("main").expect("run") }
}

const ALPHA: &str = "pub fn pick(a: i64, b: i64) -> i64:\n    a + b + 100\n";

#[test]
fn import_of_other_arity_beats_own_definition_by_arguments() {
    let beta = "use alpha.{pick}\n\npub fn pick(n: i64) -> i64:\n    n\n\n\
                pub fn beta_imported() -> i64:\n    pick(1, 2)\n\n\
                pub fn beta_own() -> i64:\n    pick(7)\n";
    let mir_module = lower(
        &[("alpha.spl", ALPHA), ("beta.spl", beta)],
        "use beta.{beta_imported, beta_own}\n\nfn main() -> i64:\n    beta_imported() * 1000 + beta_own()\n",
    )
    .expect("arity selects one definition");
    // Before the fix both calls ran beta's `(i64)` body: 1 * 1000 + 7.
    assert_eq!(run_main(&mir_module), 103_007);
}

#[test]
fn equally_fitting_own_and_imported_definitions_are_a_compile_error() {
    // i32 and u8 both admit the i64 literal `2` at the same (inexact) rank.
    let delta = "pub fn pick(a: i64, b: i32) -> i64:\n    a\n";
    let gamma = "use delta.{pick}\n\npub fn pick(a: i64, b: u8) -> i64:\n    a\n\n\
                 pub fn gamma_val() -> i64:\n    pick(1, 2)\n";
    let error = lower(
        &[("delta.spl", delta), ("gamma.spl", gamma)],
        "use gamma.{gamma_val}\n\nfn main() -> i64:\n    gamma_val()\n",
    )
    .expect_err("a tie must not pick silently");
    assert!(error.contains("ambiguous call to `pick`"), "{error}");
    assert!(error.contains("compiler_cross_module_private_symbol_collision"), "{error}");
}

#[test]
fn own_function_beats_spec_dsl_word_as_statement() {
    // `dsl.spl` stands in for std.spec, which defines `context` too.
    let dsl = "pub fn context(desc: text) -> i64:\n    0\n";
    let main = "use dsl.{context}\n\nvar hits: i64 = 0\n\n\
                fn context(v: i64):\n    hits = hits + v\n\n\
                fn main() -> i64:\n    context(5)\n    hits\n";
    let mir_module = lower(&[("dsl.spl", dsl)], main).expect("lowers");
    let calls_bdd = format!("{mir_module:?}").contains("rt_bdd_describe_start_rv");
    assert!(!calls_bdd, "a module's own `context` must not lower as a BDD group");
}
