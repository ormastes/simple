//! Mechanism pin: imported-function bindings in a module environment share ONE
//! empty `captured_env` instead of allocating a fresh ~600 B `Arc<CowEnv>` each.
//! A native-build shard holds ~950k such entries, so the per-binding copies were
//! ~0.5 GB of retained memory encoding nothing.
//! doc/08_tracking/bug/seed_empty_captured_env_allocated_per_import_binding_2026-08-22.md
use simple_compiler::interpreter;
use simple_compiler::value::Env;
use std::fs;
use std::sync::Arc;
use tempfile::tempdir;

const N: usize = 400;

fn run(main: &str, lib: &str, base: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("base.spl"), base).unwrap();
    fs::write(pkg.join("lib.spl"), lib).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    // Parse only: keep the `use` node so the INTERPRETER's module loader
    // (module_evaluator) evaluates `lib`, whose env imports `base.*`.
    let module = simple_parser::Parser::new(main).parse().unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let r = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    r.map_err(|e| format!("{e:?}"))
}

#[test]
fn imported_function_bindings_share_one_empty_captured_env() {
    let mut base = String::new();
    for i in 0..N {
        base.push_str(&format!("fn f{i}(x: i64) -> i64:\n    x + {i}\n"));
    }
    // `lib` imports all N functions: each becomes an env entry in lib's frozen
    // module env via filter_functions_from_value (captured_env stripped).
    let lib = "use pkg.base.*\nfn g(x: i64) -> i64:\n    f0(x) + f5(x)\n";
    let main = "use pkg.lib.*\nfn main() -> i64:\n    val r = g(1)\n    if r != 7:\n        return 1\n    0\n";
    let shared = Env::shared_empty();
    let before = Arc::strong_count(&shared);
    let rc = run(main, lib, &base);
    assert!(rc.is_ok(), "program must still run (imports resolve): {rc:?}");
    let after = Arc::strong_count(&shared);
    // Pre-fix: every imported binding got its own Arc::new(Env::new()), so the
    // shared Arc never gained a holder (after == before). Post-fix the importing
    // module's env and exports hold at least one clone per imported function.
    assert!(
        after >= before + N,
        "expected >= {N} bindings to share the empty captured env, got {} new holders",
        after - before
    );
    drop(shared);
    interpreter::clear_module_cache();
}
