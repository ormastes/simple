// Owner ruling 2026-09-27: closures capture enclosing locals by value and are
// read-only (.claude/rules/language.md:22). A nested fn or lambda assigning an
// enclosing local used to lose the write silently (the caller kept 0); it must
// now fail loudly when the module is loaded, for every engine that loads it.

use std::collections::HashSet;
use std::fs;

use simple_compiler::pipeline::module_loader::load_module_with_imports;
use tempfile::tempdir;

fn load(src: &str) -> Result<(), String> {
    let dir = tempdir().unwrap();
    let path = dir.path().join("main.spl");
    fs::write(&path, src).unwrap();
    load_module_with_imports(&path, &mut HashSet::new())
        .map(|_| ())
        .map_err(|e| format!("{e}"))
}

#[test]
fn nested_fn_write_to_enclosing_local_fails_to_load() {
    let err = load("fn outer() -> i64:\n    var n = 0\n    fn bump():\n        n = n + 1\n    bump()\n    n\n\nfn main() -> i64:\n    outer()\n")
        .expect_err("a nested fn assigning an enclosing local must not load");
    assert!(
        err.contains("cannot assign to captured variable `n` inside nested fn `bump` (line 4)"),
        "unexpected diagnostic: {err}"
    );
}

#[test]
fn lambda_write_to_enclosing_local_fails_to_load() {
    let err = load("fn outer() -> i64:\n    var total = 0\n    [1, 2].each(\\x:\n        total = total + x\n    )\n    total\n\nfn main() -> i64:\n    outer()\n")
        .expect_err("a lambda assigning an enclosing local must not load");
    assert!(err.contains("cannot assign to captured variable `total` inside a closure"), "unexpected diagnostic: {err}");
}

#[test]
fn module_global_write_from_nested_fn_still_loads() {
    load("var g = 0\n\nfn outer():\n    fn setg():\n        g = 5\n    setg()\n\nfn main() -> i64:\n    outer()\n    g\n")
        .expect("module globals are not captures and stay writable");
}
