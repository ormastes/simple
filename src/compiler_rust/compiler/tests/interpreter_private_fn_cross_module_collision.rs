//! Two modules each declare a PRIVATE fn with the same name and the same
//! parameter types. A call binds to the calling module's own definition; a
//! private fn of another module is never a candidate unless imported.
//!
//! Bug: doc/08_tracking/bug/seed_private_fn_cross_module_collision_2026-11-24.md
//! (`protocol_media_parts_spec._text_part` ran `serving_pooling._text_part`).

use simple_compiler::interpreter;
use simple_compiler::pipeline::module_loader::load_module_with_imports;
use simple_parser::Parser;
use std::collections::HashSet;
use std::fs;
use std::sync::{Mutex, MutexGuard};
use tempfile::tempdir;

/// The library half: its own private `_part`, reached only through `lib_part`,
/// plus `apply`, which invokes a closure handed in by the importer.
const LIB: &str = r#"fn _part(s: text) -> i64:
    100 + s.len()

pub fn lib_part(s: text) -> i64:
    _part(s)

pub fn apply(f) -> i64:
    f()
"#;

/// A module between the entry and the library, so the entry never names the
/// library (the reported spec reaches `serving_pooling` through `api_server`).
const MID: &str = r#"use partlib.{lib_part}

pub fn mid_part(s: text) -> i64:
    lib_part(s)
"#;

/// Interpreter state is process-global; a reset racing another test's
/// evaluation corrupts it (see `interpreter_flattened_module_globals.rs`).
static INTERP_TEST_LOCK: Mutex<()> = Mutex::new(());

fn interp_lock() -> MutexGuard<'static, ()> {
    INTERP_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

/// `flattened`: imports inlined by the pipeline loader before evaluation;
/// otherwise the entry is evaluated as parsed and `use` loads at run time.
fn run(flattened: bool, main: &str) -> Result<i32, String> {
    let dir = tempdir().expect("create temporary package");
    fs::write(dir.path().join("partlib.spl"), LIB).expect("write lib module");
    fs::write(dir.path().join("partmid.spl"), MID).expect("write mid module");
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, main).expect("write entry module");

    let _serial = interp_lock();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::clear_bdd_state();
    let items = if flattened {
        load_module_with_imports(&main_path, &mut HashSet::new())
            .map_err(|error| error.to_string())?
            .items
    } else {
        Parser::new(main).parse().map_err(|error| error.to_string())?.items
    };
    interpreter::set_current_file(Some(main_path));
    let result = interpreter::evaluate_module(&items);
    interpreter::set_current_file(None);
    result.map_err(|error| error.to_string())
}

fn assert_both_loaders(main: &str, expected: i32) {
    assert_eq!(run(true, main), Ok(expected), "flattened loader");
    assert_eq!(run(false, main), Ok(expected), "run-time `use` loader");
}

/// The reported shape: the call sits in an `it` body of the entry (spec) file.
#[test]
fn it_body_call_binds_to_the_entrys_own_private_fn() {
    assert_both_loaders(
        r#"use partlib.{lib_part}

fn _part(t: text) -> i64:
    t.len()

var own = 0
var theirs = 0
describe "g":
    it "x":
        own = _part("ab")
        theirs = lib_part("ab")
main = own * 1000 + theirs
"#,
        2102,
    );
}

/// The entry never names the library; it arrives through `mid`.
#[test]
fn it_body_call_binds_to_own_private_fn_when_the_other_module_loads_transitively() {
    assert_both_loaders(
        r#"use partmid.{mid_part}

fn _part(t: text) -> i64:
    t.len()

var own = 0
var theirs = 0
describe "g":
    it "x":
        own = _part("ab")
        theirs = mid_part("ab")
main = own * 1000 + theirs
"#,
        2102,
    );
}

/// The entry's definition written BEFORE the import, so neither registration
/// order can make the entry's own fn win by accident.
#[test]
fn it_body_call_binds_to_own_private_fn_declared_before_the_import() {
    assert_both_loaders(
        r#"fn _part(t: text) -> i64:
    t.len()

use partlib.{lib_part}

var own = 0
var theirs = 0
describe "g":
    it "x":
        own = _part("ab")
        theirs = lib_part("ab")
main = own * 1000 + theirs
"#,
        2102,
    );
}

/// Entry top-level code (no enclosing function, no closure).
#[test]
fn top_level_call_binds_to_the_entrys_own_private_fn() {
    assert_both_loaders(
        r#"use partlib.{lib_part}

fn _part(t: text) -> i64:
    t.len()

main = _part("ab") * 1000 + lib_part("ab")
"#,
        2102,
    );
}

/// A closure written in the entry and invoked by a library function runs
/// with the library as the executing module; it still names the entry's fn.
#[test]
fn closure_invoked_by_the_other_module_binds_to_its_writers_private_fn() {
    assert_both_loaders(
        r#"use partlib.{lib_part, apply}

fn _part(t: text) -> i64:
    t.len()

main = apply(\: _part("ab")) * 1000 + lib_part("ab")
"#,
        2102,
    );
}

/// Not only a tie: the other module's fn is the better-scoring overload
/// (typed parameter vs the entry's untyped one) and must still not be chosen.
#[test]
fn own_private_fn_wins_over_a_better_scoring_foreign_one() {
    assert_both_loaders(
        r#"use partlib.{lib_part}

fn _part(t) -> i64:
    7

main = _part("ab") * 1000 + lib_part("ab")
"#,
        7102,
    );
}
