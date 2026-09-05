//! Mechanism pin: the `f(obj.field)` argument write-back mutates the caller's
//! object field map IN PLACE instead of copy-on-writing it against a handle
//! that is already dead.
//!
//! The write-back read the caller's object with `outer_env.get(&obj_name)
//! .cloned()`, which leaves the frame holding the same `Arc`, so the
//! `Arc::make_mut` two lines later was *guaranteed* to deep-copy the whole
//! `HashMap<String, Value>` — on every single call — even though the binding
//! is overwritten immediately afterwards and no live alias could observe the
//! copy. `FIELD_WRITEBACK_MAP_CLONES == FIELD_WRITEBACK_CALLS` pre-fix, 0
//! post-fix.
//!
//! doc/08_tracking/bug/seed_field_writeback_copies_object_map_against_dead_alias_2026-08-23.md
use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::collections::HashSet;
use std::fs;
use std::sync::atomic::Ordering;
use tempfile::tempdir;

const CALLS: usize = 200;

fn run_program(main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    let main_path = pkg.join("main.spl");
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

/// `push_into(box.items, k)` — a plain function taking the object's array
/// field, so the callee's mutation is written back into `box.items`.
fn program(calls: usize) -> String {
    let last = calls - 1;
    [
        "class Box:",
        "    items: [i64]",
        "    tag: text",
        "",
        "fn push_into(xs: [i64], v: i64):",
        "    xs.push(v)",
        "",
        "fn main() -> i32:",
        "    var b = Box(items: [], tag: \"t\")",
        "    var k = 0",
        &format!("    while k < {calls}:"),
        "        push_into(b.items, k)",
        "        k = k + 1",
        &format!("    if b.items.len() != {calls}:"),
        "        return 1",
        &format!("    if b.items[{last}] != {last}:"),
        "        return 2",
        "    if b.tag != \"t\":",
        "        return 3",
        "    return 0",
        "",
    ]
    .join("\n")
}

#[test]
fn field_writeback_does_not_copy_the_object_map_per_call() {
    perf_counters::set_enabled(true);
    perf_counters::FIELD_WRITEBACK_CALLS.store(0, Ordering::Relaxed);
    perf_counters::FIELD_WRITEBACK_MAP_CLONES.store(0, Ordering::Relaxed);

    let rc = run_program(&program(CALLS));
    assert_eq!(rc, Ok(0), "program must run and keep both fields intact");

    let calls = perf_counters::FIELD_WRITEBACK_CALLS.load(Ordering::Relaxed);
    let clones = perf_counters::FIELD_WRITEBACK_MAP_CLONES.load(Ordering::Relaxed);
    assert!(
        calls >= CALLS as u64,
        "expected >= {CALLS} field write-backs, saw {calls}"
    );
    // Pre-fix: clones == calls (every write-back deep-copied the field map).
    assert_eq!(clones, 0, "field map copied {clones} times across {calls} write-backs");
    perf_counters::set_enabled(false);
}

/// Value semantics are unaffected: the caller still observes the callee's
/// mutation of the field it passed, and the object's other fields survive.
#[test]
fn writeback_still_publishes_the_callee_mutation() {
    let rc = run_program(&program(8));
    assert_eq!(rc, Ok(0));
}
