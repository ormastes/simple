//! Grouped imports must not let an implicit module namespace overwrite an
//! explicitly selected export with the same local name.
//!
//! Bug: doc/08_tracking/bug/module_named_like_its_class_shadows_it_inside_it_blocks_2026-08-04.md

use simple_compiler::interpreter;
use simple_parser::Parser;
use std::fs;
use std::path::Path;
use std::sync::{Mutex, MutexGuard};
use tempfile::tempdir;

static INTERP_TEST_LOCK: Mutex<()> = Mutex::new(());

fn interp_lock() -> MutexGuard<'static, ()> {
    INTERP_TEST_LOCK.lock().unwrap_or_else(|error| error.into_inner())
}

fn evaluate_unflattened(main_path: &Path) -> (i32, Vec<(String, String, bool, bool)>) {
    let _serial = interp_lock();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::clear_bdd_state();

    let source = fs::read_to_string(main_path).expect("read entry source");
    let module = Parser::new(&source).parse().expect("parse entry source");
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    let test_results = interpreter::get_test_results();
    interpreter::set_current_file(None);

    (result.expect("evaluate entry source"), test_results)
}

#[test]
fn same_name_class_and_multiple_exports_resolve_at_top_level_and_in_nested_it() {
    let dir = tempdir().expect("create temp source directory");
    fs::write(
        dir.path().join("MirProgram.spl"),
        r#"
class MirProgram:
    value: i64

    static fn empty() -> MirProgram:
        MirProgram(value: 7)

fn helper() -> i64:
    5
"#,
    )
    .expect("write imported module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        r#"
use MirProgram.{MirProgram, helper}

class Probe:
    value: i64

    fn read() -> i64:
        self.value

val top_level = MirProgram.empty()

describe "same-name grouped class":
    context "nested block":
        it "keeps selected class and self lookup":
            val nested = MirProgram.empty()
            val probe = Probe(value: nested.value + helper())
            expect(probe.read()).to_equal(12)

fn main() -> i32:
    top_level.value - 7
"#,
    )
    .expect("write entry module");

    let (exit_code, results) = evaluate_unflattened(&main_path);
    assert_eq!(
        exit_code, 0,
        "top-level selected class must not become a module dictionary"
    );
    assert_eq!(results.len(), 1, "the nested BDD example must execute exactly once");
    assert!(
        results[0].2,
        "the nested BDD example must resolve the selected class and self"
    );
    assert!(!results[0].3, "the nested BDD example must not be skipped");
}

#[test]
fn non_conflicting_group_retains_module_namespace_for_qualified_access() {
    let dir = tempdir().expect("create temp source directory");
    fs::write(
        dir.path().join("syntax.spl"),
        r#"
class Parser:
    value: i64

fn answer() -> i64:
    40
"#,
    )
    .expect("write imported module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        r#"
use syntax.{Parser}

fn main() -> i32:
    val parser = Parser(value: 2)
    syntax.answer() + parser.value - 42
"#,
    )
    .expect("write entry module");

    assert_eq!(evaluate_unflattened(&main_path).0, 0);
}

#[test]
fn explicit_module_alias_retains_qualified_access() {
    let dir = tempdir().expect("create temp source directory");
    fs::write(dir.path().join("MirProgram.spl"), "fn answer() -> i64:\n    42\n").expect("write imported module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use MirProgram as mir_module\n\nfn main() -> i32:\n    mir_module.answer() - 42\n",
    )
    .expect("write entry module");

    assert_eq!(evaluate_unflattened(&main_path).0, 0);
}

#[test]
fn absent_same_name_export_does_not_hide_module_namespace() {
    let dir = tempdir().expect("create temp source directory");
    fs::write(dir.path().join("Widget.spl"), "fn answer() -> i64:\n    42\n").expect("write imported module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "use Widget.{Widget}\n\nfn main() -> i32:\n    Widget.answer() - 42\n",
    )
    .expect("write entry module");

    assert_eq!(evaluate_unflattened(&main_path).0, 0);
}

#[test]
fn path_derived_main_namespace_remains_suppressed() {
    let dir = tempdir().expect("create temp source directory");
    let tools_dir = dir.path().join("tools");
    fs::create_dir(&tools_dir).expect("create imported module directory");
    fs::write(tools_dir.join("main.spl"), "fn answer() -> i64:\n    42\n").expect("write imported module");
    let main_path = dir.path().join("entry.spl");
    fs::write(&main_path, "use tools.main.{answer}\n\nanswer() - 42\n").expect("write entry module");

    assert_eq!(evaluate_unflattened(&main_path).0, 0);
}

#[test]
fn duplicate_group_alias_keeps_existing_last_selected_binding_policy() {
    let dir = tempdir().expect("create temp source directory");
    fs::write(
        dir.path().join("Choice.spl"),
        r#"
fn first() -> i64:
    1

fn second() -> i64:
    2
"#,
    )
    .expect("write imported module");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        r#"
use Choice.{first as Choice, second as Choice}

fn main() -> i32:
    Choice() - 2
"#,
    )
    .expect("write entry module");

    assert_eq!(evaluate_unflattened(&main_path).0, 0);
}
