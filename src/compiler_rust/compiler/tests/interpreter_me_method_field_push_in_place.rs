//! Mechanism pin: `self.items.push(x)` inside a `me` method called on a LOCAL
//! receiver mutates the backing Vec in place. Before the fix the caller kept an
//! `Arc` alias of the receiver's field map for the whole call, so
//! `Arc::make_mut` deep-copied the array on every push: O(n) per call, O(n^2)
//! per accumulation loop (16k pushes = 1.5 s in the seed interpreter).
//! doc/08_tracking/bug/me_method_self_field_push_deep_copies_per_call_2026-08-22.md
use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::collections::HashSet;
use std::fs;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

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

fn program(pushes: usize) -> String {
    let last = pushes - 1;
    [
        "class Acc:",
        "    count: i64",
        "    items: [i64]",
        "",
        "    static fn new() -> Acc:",
        "        Acc(count: 0, items: [])",
        "",
        "    me add(v: i64):",
        "        self.count = self.count + v",
        "        self.items.push(v)",
        "",
        "fn main() -> i32:",
        "    var a = Acc.new()",
        "    var k = 0",
        &format!("    while k < {pushes}:"),
        "        a.add(k)",
        "        k = k + 1",
        &format!("    if a.items.len() != {pushes}:"),
        "        return 1",
        &format!("    if a.items[{last}] != {last}:"),
        "        return 2",
        "    return 0",
        "",
    ]
    .join("\n")
}

fn time_pushes(pushes: usize) -> Duration {
    let start = Instant::now();
    let result = run_program(&program(pushes));
    let elapsed = start.elapsed();
    assert_eq!(
        result,
        Ok(0),
        "program with {pushes} pushes must run and keep its contents"
    );
    elapsed
}

#[test]
fn me_method_self_field_push_does_not_clone_the_array_per_call() {
    // Counter pin (the mechanism): with the caller's alias released for the
    // duration of the body, the receiver's field array is uniquely owned and
    // the in-place path must never hit the COW-clone branch.
    perf_counters::set_enabled(true);
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let before_calls = perf_counters::SELF_FIELD_ARR_MUT_CALLS.load(Ordering::Relaxed);
    let before_clones = perf_counters::SELF_FIELD_ARR_COW_CLONES.load(Ordering::Relaxed);
    let n = 2_000;
    assert_eq!(run_program(&program(n)), Ok(0));
    let calls = perf_counters::SELF_FIELD_ARR_MUT_CALLS.load(Ordering::Relaxed) - before_calls;
    let clones = perf_counters::SELF_FIELD_ARR_COW_CLONES.load(Ordering::Relaxed) - before_clones;
    eprintln!("[me-push] {n} pushes: in-place calls={calls} cow-clones={clones}");
    assert!(
        calls >= n as u64,
        "the in-place field-array path must handle every push (got {calls})"
    );
    assert_eq!(
        clones, 0,
        "self.items.push inside a me method deep-copied the array {clones} times"
    );
}

#[test]
fn me_method_self_field_push_scales_linearly() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let _ = time_pushes(500);
    let small = time_pushes(2_000);
    let large = time_pushes(8_000);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(0.001);
    eprintln!("[me-push] 2000 pushes {small:?}, 8000 pushes {large:?}, ratio {ratio:.2} (linear ~4, quadratic ~16)");
    assert!(
        ratio < 9.0,
        "self.items.push in a me method is super-linear: x4 pushes cost x{ratio:.1}"
    );
}

#[test]
fn aliased_receiver_still_copies_on_write() {
    // Value semantics: a second holder of the object must not observe the push.
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let src: String = [
        "class Acc:",
        "    items: [i64]",
        "",
        "    static fn new() -> Acc:",
        "        Acc(items: [])",
        "",
        "    me add(v: i64):",
        "        self.items.push(v)",
        "",
        "fn main() -> i32:",
        "    var a = Acc.new()",
        "    a.add(1)",
        "    val snapshot = a",
        "    a.add(2)",
        "    a.add(3)",
        "    if snapshot.items.len() != 1:",
        "        return 1",
        "    if a.items.len() != 3:",
        "        return 2",
        "    return 0",
        "",
    ]
    .join("\n");
    assert_eq!(run_program(&src), Ok(0));
}

#[test]
fn argument_reading_the_receiver_still_sees_it() {
    // `c.add(c.count)` evaluates the argument before the receiver is released.
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let src: String = [
        "class Acc:",
        "    count: i64",
        "    items: [i64]",
        "",
        "    static fn new() -> Acc:",
        "        Acc(count: 5, items: [])",
        "",
        "    me add(v: i64):",
        "        self.count = self.count + 1",
        "        self.items.push(v)",
        "",
        "fn main() -> i32:",
        "    var a = Acc.new()",
        "    a.add(a.count)",
        "    a.add(a.count)",
        "    if a.items[0] != 5:",
        "        return 1",
        "    if a.items[1] != 6:",
        "        return 2",
        "    if a.count != 7:",
        "        return 3",
        "    return 0",
        "",
    ]
    .join("\n");
    assert_eq!(run_program(&src), Ok(0));
}
