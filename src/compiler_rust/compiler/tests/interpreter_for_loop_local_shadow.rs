// A `for` loop variable must not be aliased to a same-named module global.
//
// Until 2026-08-21 `exec_for` saved/restored the loop binding's prior value but
// never marked it local (`enter_block_local`). `env.is_local(name)` was
// therefore false for the loop variable, so the globals write-back that runs
// after any call in the loop body (`sync_owned_captured_globals` ->
// `refresh_bound_global` in interpreter_call/core/function_exec.rs) treated the
// loop variable as a local alias of the imported module global of the same
// name and overwrote it -- and published the loop value into the module global
// on the way out. Symptom: `for name in ...:` read back "Alice", the value of
// `val name = "Alice"` in a wildcard-imported module.
// doc/08_tracking/bug/seed_interpreter_module_global_clobbers_function_local_2026-08-21.md

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_pkg_program(lib: &str, main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("lib.spl"), lib).unwrap();
    // The entry file must sit OUTSIDE the package directory: only then does
    // `use pkg.lib.*` resolve through the package root and give the entry
    // frame an owner scope whose import table aliases `name` to pkg.lib's
    // global. An entry inside `src/pkg/` resolves the import differently and
    // does NOT reproduce the defect (measured 2026-08-21).
    let main_path = dir.path().join("entry.spl");
    fs::write(&main_path, main).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.map_err(|e| format!("{e:?}"))
}

const LIB: &str = "fn touch(label: text, actual: i64, expected: i64):\n    if actual != expected:\n        print \"FAIL: {label}\"\n\nval name = \"Alice\"\ntouch(\"seed\", 1, 1)\n";

/// The reported shape: `for` over a split, calling into the module that owns
/// the same-named global. Returns 1 if the loop variable was clobbered.
#[test]
fn for_loop_variable_is_not_clobbered_by_same_named_module_global() {
    let main = "use pkg.lib.*\n\nfn main() -> i32:\n    var bad = 0\n    var seen = \"\"\n    for name in \"aa,bb\".split(\",\"):\n        touch(\"x\", 1, 1)\n        seen = seen + name\n        if name == \"Alice\":\n            bad = 1\n    if seen != \"aabb\":\n        bad = 1\n    return bad\n";
    assert_eq!(
        run_pkg_program(LIB, main),
        Ok(0),
        "for-loop variable `name` must keep its iteration value across a cross-module call"
    );
}

/// The write-back direction: the module global must not be overwritten by the
/// loop variable either.
#[test]
fn for_loop_variable_does_not_publish_into_the_module_global() {
    let main = "use pkg.lib.*\n\nfn main() -> i32:\n    for name in \"aa,bb\".split(\",\"):\n        touch(\"x\", 1, 1)\n    if name != \"Alice\":\n        return 1\n    return 0\n";
    assert_eq!(
        run_pkg_program(LIB, main),
        Ok(0),
        "the module global `name` must still be \"Alice\" after the loop"
    );
}

/// Nested shape: the collision on an inner loop must not damage the outer one.
#[test]
fn nested_for_loops_keep_their_own_bindings() {
    let main = "use pkg.lib.*\n\nfn main() -> i32:\n    var acc = \"\"\n    for name in \"a,b\".split(\",\"):\n        for name2 in \"1,2\".split(\",\"):\n            touch(\"x\", 1, 1)\n            acc = acc + name + name2\n    if acc != \"a1a2b1b2\":\n        return 1\n    return 0\n";
    assert_eq!(run_pkg_program(LIB, main), Ok(0), "nested loop bindings must not alias globals");
}
