//! Import-cycle reporting.
//!
//! The module loader has always *detected* import cycles -- `loaded_modules` is
//! the active import path, so re-entering a module still on it is exactly a
//! cycle -- but it absorbed them silently and returned `Ok(())`. The dedicated
//! reporter, `ModuleResolver::check_circular_dependencies`, is unreachable: its
//! `ImportGraph` is only ever fed by `record_import`, whose sole callers are
//! unit tests, so in production the graph is empty and the check is a
//! guaranteed `Ok(())`.
//!
//! These tests pin the cycle down where the real graph is actually walked.

use simple_compiler::hir::Lowerer;
use simple_compiler::module_resolver::ModuleResolver;
use simple_parser::Parser;
use std::fs;
use tempfile::tempdir;

fn lower_entry(dir: &std::path::Path, src: &std::path::Path, entry: &std::path::Path) -> Vec<String> {
    let source = fs::read_to_string(entry).unwrap();
    let mut parser = Parser::new(&source);
    let ast = parser.parse().expect("parse failed");
    let resolver = ModuleResolver::new(dir.to_path_buf(), src.to_path_buf());
    let mut lowerer = Lowerer::with_module_resolver(resolver, entry.to_path_buf());
    lowerer
        .lower_module_with_warnings(&ast)
        .expect("lowering should still succeed -- cycles are reported, not rejected")
        .import_cycles
}

#[test]
fn reports_a_two_module_import_cycle() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let pkg = src.join("pkg");
    fs::create_dir_all(&pkg).unwrap();

    // Each module re-exports the same name from the other. The loader follows a
    // re-export only when it can supply the requested symbol, so this is the
    // shape that actually walks the import graph in a circle.
    fs::write(
        pkg.join("alpha.spl"),
        "use pkg.beta (shared_value)\n\nfn alpha_value() -> i64:\n    1\n",
    )
    .unwrap();
    fs::write(
        pkg.join("beta.spl"),
        "use pkg.alpha (shared_value)\n\nfn beta_value() -> i64:\n    2\n",
    )
    .unwrap();

    let cycles = lower_entry(dir.path(), &src, &pkg.join("alpha.spl"));

    assert!(
        !cycles.is_empty(),
        "a mutual import must be reported as a cycle, got none"
    );
    let joined = cycles.join(" | ");
    assert!(
        joined.contains("alpha.spl") && joined.contains("beta.spl"),
        "cycle must name both modules, got: {joined}"
    );
    assert!(
        joined.contains(" -> "),
        "cycle must be rendered as a path, got: {joined}"
    );
}

#[test]
fn reports_a_three_module_import_cycle() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let pkg = src.join("pkg");
    fs::create_dir_all(&pkg).unwrap();

    fs::write(
        pkg.join("one.spl"),
        "use pkg.two (shared_value)\n\nfn one_value() -> i64:\n    1\n",
    )
    .unwrap();
    fs::write(
        pkg.join("two.spl"),
        "use pkg.three (shared_value)\n\nfn two_value() -> i64:\n    2\n",
    )
    .unwrap();
    fs::write(
        pkg.join("three.spl"),
        "use pkg.one (shared_value)\n\nfn three_value() -> i64:\n    3\n",
    )
    .unwrap();

    let cycles = lower_entry(dir.path(), &src, &pkg.join("one.spl"));

    assert!(!cycles.is_empty(), "a three-module cycle must be reported, got none");
    let joined = cycles.join(" | ");
    for module in ["one.spl", "two.spl", "three.spl"] {
        assert!(joined.contains(module), "cycle must name {module}, got: {joined}");
    }
}

/// The honest direction. A check that reports a cycle for acyclic imports would
/// be as useless as one that reports nothing.
#[test]
fn reports_no_cycle_for_an_acyclic_import_chain() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let pkg = src.join("pkg");
    fs::create_dir_all(&pkg).unwrap();

    fs::write(
        pkg.join("top.spl"),
        "use pkg.middle (shared_value)\n\nfn top_value() -> i64:\n    1\n",
    )
    .unwrap();
    fs::write(
        pkg.join("middle.spl"),
        "use pkg.leaf (shared_value)\n\nfn middle_value() -> i64:\n    2\n",
    )
    .unwrap();
    fs::write(pkg.join("leaf.spl"), "fn shared_value() -> i64:\n    1\n").unwrap();

    let cycles = lower_entry(dir.path(), &src, &pkg.join("top.spl"));

    assert!(
        cycles.is_empty(),
        "an acyclic import chain must report no cycles, got: {cycles:?}"
    );
}

/// A module importing two modules that both import a common leaf is a diamond,
/// not a cycle. The leaf is visited twice but never while it is on the active
/// path, so it must not be reported.
#[test]
fn reports_no_cycle_for_a_diamond_import_graph() {
    let dir = tempdir().unwrap();
    let src = dir.path().join("src");
    let pkg = src.join("pkg");
    fs::create_dir_all(&pkg).unwrap();

    fs::write(
        pkg.join("root.spl"),
        "use pkg.left (shared_value)\nuse pkg.right (shared_value)\n\nfn root_value() -> i64:\n    1\n",
    )
    .unwrap();
    fs::write(
        pkg.join("left.spl"),
        "use pkg.shared (shared_value)\n\nfn left_value() -> i64:\n    2\n",
    )
    .unwrap();
    fs::write(
        pkg.join("right.spl"),
        "use pkg.shared (shared_value)\n\nfn right_value() -> i64:\n    3\n",
    )
    .unwrap();
    fs::write(pkg.join("shared.spl"), "fn shared_value() -> i64:\n    5\n").unwrap();

    let cycles = lower_entry(dir.path(), &src, &pkg.join("root.spl"));

    assert!(
        cycles.is_empty(),
        "a diamond is not a cycle and must not be reported, got: {cycles:?}"
    );
}
