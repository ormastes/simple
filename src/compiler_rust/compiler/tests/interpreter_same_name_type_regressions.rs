//! Flattened-interpreter regressions for same-named types from distinct modules.
//!
//! Covers cross_module_class_name_collision_resolution_2026-08-17 and the
//! List/Iterable shape from lexer_spec_list_iterable_symbol_collision_2026-09-01.

use simple_compiler::interpreter;
use simple_compiler::pipeline::module_loader::load_module_with_imports;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_modules(modules: &[(&str, &str)], main: &str) -> Result<i32, String> {
    let dir = tempdir().expect("create temporary package");
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).expect("create package directory");
    for (name, source) in modules {
        fs::write(pkg.join(format!("{name}.spl")), source).expect("write module");
    }
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).expect("write entry module");

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = load_module_with_imports(&main_path, &mut HashSet::new()).map_err(|error| error.to_string())?;
    interpreter::set_current_file(Some(main_path));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.map_err(|error| error.to_string())
}

#[test]
fn same_named_classes_resolve_fields_in_their_declaring_modules() {
    let result = run_modules(
        &[
            (
                "loader",
                r#"pub class ModuleLoader:
    compiler_ctx_cell: i64

fn loader_context() -> i64:
    val loader = ModuleLoader(compiler_ctx_cell: 17)
    loader.compiler_ctx_cell
"#,
            ),
            (
                "compat",
                r#"pub class ModuleLoader:
    compat_tag: i64

fn compat_context() -> i64:
    val loader = ModuleLoader(compat_tag: 29)
    loader.compat_tag
"#,
            ),
        ],
        r#"use pkg.loader.{loader_context}
use pkg.compat.{compat_context}

fn main() -> i32:
    if loader_context() != 17:
        return 1
    if compat_context() != 29:
        return 2
    0
"#,
    );

    assert_eq!(result, Ok(0));
}

#[test]
fn duplicate_list_class_does_not_break_iterable_conformance() {
    let result = run_modules(
        &[
            (
                "iterable",
                r#"pub trait Iterable<T>:
    fn iter() -> i64
"#,
            ),
            (
                "list_a",
                r#"use pkg.iterable.{Iterable}

pub class List<T>:
    items: [T]

impl Iterable<T> for List<T>:
    fn iter() -> i64:
        7

fn list_a_iter() -> i64:
    val values = List<i64>(items: [1, 2])
    values.iter()
"#,
            ),
            (
                "list_b",
                r#"pub class List<T>:
    items: [T]

fn list_b_len() -> i64:
    val values = List<i64>(items: [4, 5, 6])
    values.items.len()
"#,
            ),
        ],
        r#"use pkg.list_a.{list_a_iter}
use pkg.list_b.{list_b_len}

fn main() -> i32:
    if list_a_iter() != 7:
        return 1
    if list_b_len() != 3:
        return 2
    0
"#,
    );

    assert_eq!(result, Ok(0));
}
