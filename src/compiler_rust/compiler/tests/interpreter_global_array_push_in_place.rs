//! Mechanism pin: `global_array.push(x)` inside a function mutates the backing
//! Vec in place. Before the fix `Env::get_mut` promoted the global into the
//! frame overlay by cloning its `Arc` while the store, the frame's scope
//! snapshot, caller frames' refreshed copies and a stray temporary all kept
//! theirs, so `Arc::make_mut` deep-copied the array once per frame: O(n) per
//! push, O(n^2) per accumulation -- the parser pushes ~70 flat-AST pools per
//! node from a fresh frame each time, which is how a 6107-line module took 20
//! minutes to parse.
//! doc/08_tracking/bug/seed_global_array_push_cow_per_frame_2026-08-22.md
use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::collections::HashSet;
use std::fs;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

fn run_program(main: &str) -> Result<i32, String> {
    run_modules(POOLS, main)
}

/// The parser's shape: the pools and the leaf allocator live in an IMPORTED
/// module (owned globals, scope snapshots, cross-module bindings), driven
/// from a loop in the entry module. A single evaluated file has no module
/// owner and takes a different global path.
const POOLS: &str = "var pool: [i64] = []\nvar other: [i64] = []\n\nfn alloc(v: i64) -> i64:\n    val idx = pool.len()\n    pool.push(v)\n    other.push(v * 2)\n    idx\n\nfn pool_len() -> i64:\n    pool.len()\n\nfn pool_at(i: i64) -> i64:\n    pool[i]\n\nfn other_at(i: i64) -> i64:\n    other[i]\n";

fn run_modules(pools: &str, main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("pools.spl"), pools).unwrap();
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

/// The parser's shape: one global pool pushed from a leaf function that is
/// called once per element from a loop in another function.
fn program(pushes: usize) -> String {
    let last = pushes - 1;
    [
        "use pools.{alloc, pool_len, pool_at, other_at}",
        "",
        "fn main() -> i32:",
        "    var k = 0",
        &format!("    while k < {pushes}:"),
        "        val _i = alloc(k)",
        "        k = k + 1",
        &format!("    if pool_len() != {pushes}:"),
        "        return 1",
        &format!("    if pool_at({last}) != {last}:"),
        "        return 2",
        &format!("    if other_at({last}) != {last} * 2:"),
        "        return 3",
        "    return 0",
        "",
    ]
    .join("\n")
}

fn time_pushes(pushes: usize) -> Duration {
    let start = Instant::now();
    let result = run_program(&program(pushes));
    let elapsed = start.elapsed();
    assert_eq!(result, Ok(0), "program with {pushes} pushes must run and keep its contents");
    elapsed
}

#[test]
fn global_array_push_in_a_function_does_not_clone_per_frame() {
    perf_counters::set_enabled(true);
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let before_calls = perf_counters::ARR_MUT_CALLS.load(Ordering::Relaxed);
    let before_clones = perf_counters::ARR_MUT_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    let n = 2_000;
    assert_eq!(run_program(&program(n)), Ok(0));
    let calls = perf_counters::ARR_MUT_CALLS.load(Ordering::Relaxed) - before_calls;
    let elems = perf_counters::ARR_MUT_COW_ELEMS_CLONED.load(Ordering::Relaxed) - before_clones;
    eprintln!("[global-push] {n} allocs: in-place calls={calls} cow-elements-cloned={elems}");
    assert!(calls >= 2 * n as u64, "the in-place path must handle every push (got {calls})");
    // Pre-fix this is ~n^2 (two pools x n frames x growing length = ~4M).
    // A handful of element copies from one-off promotions is fine; a per-frame
    // deep copy is not.
    assert!(elems < 10 * n as u64, "global pushes deep-copied {elems} elements for {n} allocs (quadratic)");
}

#[test]
fn global_array_push_scales_linearly() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let _ = time_pushes(500);
    let small = time_pushes(2_000);
    let large = time_pushes(8_000);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(0.001);
    eprintln!("[global-push] 2000 allocs {small:?}, 8000 allocs {large:?}, ratio {ratio:.2} (linear ~4, quadratic ~16)");
    assert!(ratio < 9.0, "global array push from a function is super-linear: x4 allocs cost x{ratio:.1}");
}

#[test]
fn aliased_global_still_copies_on_write() {
    // Value semantics: a snapshot of the global taken before the push must
    // not observe it, and the caller must see the push after the call.
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let pools = "var pool: [i64] = []\n\nfn alloc(v: i64):\n    pool.push(v)\n\nfn check() -> i32:\n    alloc(1)\n    val snapshot = pool\n    alloc(2)\n    alloc(3)\n    if snapshot.len() != 1:\n        return 1\n    if pool.len() != 3:\n        return 2\n    0\n";
    let main = "use pools.{check}\n\nfn main() -> i32:\n    check()\n";
    assert_eq!(run_modules(pools, main), Ok(0));
}

#[test]
fn callee_sees_the_push_made_before_the_call() {
    // The store holds a placeholder between promotion and publish; a nested
    // call publishes first, so the callee must read the pushed contents.
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let pools = "var pool: [i64] = []\n\nfn count() -> i64:\n    pool.len()\n\nfn alloc(v: i64) -> i64:\n    pool.push(v)\n    val seen = count()\n    pool.push(v + 100)\n    seen\n\nfn check() -> i32:\n    if alloc(1) != 1:\n        return 1\n    if alloc(2) != 3:\n        return 2\n    if pool.len() != 4:\n        return 3\n    if pool[3] != 102:\n        return 4\n    0\n";
    let main = "use pools.{check}\n\nfn main() -> i32:\n    check()\n";
    assert_eq!(run_modules(pools, main), Ok(0));
}

#[test]
fn cross_module_caller_sees_pushes_and_reads_after_push_see_them() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let pools = "var pool: [text] = []\n\nfn alloc(v: text) -> text:\n    pool.push(v)\n    pool[pool.len() - 1]\n\nfn pool_len() -> i64:\n    pool.len()\n";
    let main = "use pools.{alloc, pool_len}\n\nfn main() -> i32:\n    if alloc(\"a\") != \"a\":\n        return 1\n    if alloc(\"b\") != \"b\":\n        return 2\n    if pool_len() != 2:\n        return 3\n    return 0\n";
    assert_eq!(run_modules(pools, main), Ok(0));
}
