//! Native (non-flattened) lane: an enum the entry file explicitly `use`s must
//! win over a same-named enum with different variants that a transitively
//! imported module loads later. Regression for
//! doc/08_tracking/bug/seed_enum_bare_name_collision_native_2026-11-14.md
use crate::hir::lower::lowerer::Lowerer;
use crate::module_resolver::ModuleResolver;
use crate::test_helpers::create_test_project;
use simple_parser::Parser;
use std::fs;

fn lower_entry_to_mir(files: &[(&str, &str)], entry: &str) -> Result<(), String> {
    let dir = create_test_project();
    let src = dir.path().join("src");
    for (name, text) in files {
        fs::write(src.join(name), text).unwrap();
    }
    let ast = Parser::new(entry).parse().expect("parse entry");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let hir = Lowerer::with_module_resolver(resolver, src.join("main.spl"))
        .lower_module(&ast)
        .map_err(|e| format!("hir: {e}"))?;
    crate::mir::lower_to_mir(&hir).map(|_| ()).map_err(|e| format!("mir: {e}"))
}

const A_TYPES: &str = "enum Status:\n    OnlyInA\n    AlsoA\n";
const B_TYPES: &str = "enum Status:\n    OnlyInB\n    AlsoB\n";
const A_FACADE: &str = "export use a_types.{Status}\n";
const B_USER: &str = "use b_types.{Status}\n\nfn b_helper() -> i64:\n    val s = Status.OnlyInB\n    0\n";

#[test]
fn explicit_import_wins_over_later_transitive_same_named_enum() {
    let entry = "use a_types.{Status}\nuse b_user.{b_helper}\n\nfn probe() -> Status:\n    Status.OnlyInA\n";
    let result = lower_entry_to_mir(
        &[("a_types.spl", A_TYPES), ("b_types.spl", B_TYPES), ("b_user.spl", B_USER)],
        entry,
    );
    assert_eq!(result, Ok(()));
}

#[test]
fn explicit_facade_import_wins_over_later_transitive_same_named_enum() {
    let entry = "use a_facade.{Status}\nuse b_user.{b_helper}\n\nfn probe() -> Status:\n    Status.OnlyInA\n";
    let result = lower_entry_to_mir(
        &[("a_types.spl", A_TYPES), ("a_facade.spl", A_FACADE), ("b_types.spl", B_TYPES), ("b_user.spl", B_USER)],
        entry,
    );
    assert_eq!(result, Ok(()));
}
