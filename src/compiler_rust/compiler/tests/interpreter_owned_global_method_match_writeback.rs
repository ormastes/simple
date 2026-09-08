//! A mutating method called on an owner-scoped module global must publish its
//! updated receiver to both global stores before a match arm refreshes the
//! caller frame.

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_pkg(state: &str, main: &str) -> i32 {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("state.spl"), state).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.clone()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    match result {
        Ok(code) => code,
        Err(error) => panic!("program failed: {error:?}"),
    }
}

const COUNTER_MODULE: &str = r#"class Counter:
    value: i64

impl Counter:
    me bump() -> Result<i64, text>:
        self.value = self.value + 1
        Ok(self.value)

var COUNTER = Counter(value: 0)

fn bump_in_match() -> i64:
    val observed = match COUNTER.bump():
        case Err(_): -1
        case Ok(value): value
    COUNTER.value * 10 + observed
"#;

#[test]
fn match_subject_method_keeps_owned_global_receiver_update() {
    let code = run_pkg(
        COUNTER_MODULE,
        r#"use pkg.state (bump_in_match)

fn main() -> i32:
    if bump_in_match() != 11:
        return 1
    if bump_in_match() != 22:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn aliased_import_receiver_updates_the_source_owner() {
    let code = run_pkg(
        COUNTER_MODULE,
        r#"use pkg.state.{COUNTER as imported_counter}

fn main() -> i32:
    val first = match imported_counter.bump():
        case Err(_): -1
        case Ok(value): value
    val second = match imported_counter.bump():
        case Err(_): -1
        case Ok(value): value
    if first != 1 or second != 2 or imported_counter.value != 2:
        return 1
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn local_shadow_and_nested_control_flow_do_not_clobber_the_global() {
    let state = format!(
        "{}\nfn nested_and_shadowed() -> i64:\n    var COUNTER = Counter(value: 100)\n    var local = 0\n    if true:\n        val observed = match COUNTER.bump():\n            case Err(_): -1\n            case Ok(value): value\n        local = observed + COUNTER.value\n    local\n",
        COUNTER_MODULE
    );
    let code = run_pkg(
        &state,
        r#"use pkg.state (nested_and_shadowed, bump_in_match)

fn main() -> i32:
    if nested_and_shadowed() != 202:
        return 1
    if bump_in_match() != 11:
        return 2
    0
"#,
    );
    assert_eq!(code, 0);
}

#[test]
fn entry_global_receiver_survives_match_refresh() {
    let code = run_pkg(
        "",
        r#"class Counter:
    value: i64

impl Counter:
    me bump() -> Result<i64, text>:
        self.value = self.value + 1
        Ok(self.value)

var COUNTER = Counter(value: 0)

fn main() -> i32:
    val observed = match COUNTER.bump():
        case Err(_): -1
        case Ok(value): value
    if observed != 1 or COUNTER.value != 1:
        return 1
    0
"#,
    );
    assert_eq!(code, 0);
}
