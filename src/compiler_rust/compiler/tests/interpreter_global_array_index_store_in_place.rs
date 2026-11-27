//! Mechanism pin: `global_array[i] = v` inside a module function mutates the
//! backing Vec in place. Before the fix an owner-bound global (it has a
//! `global_binding`, so it is not `is_module_global`) took node_exec.rs's
//! generic index-store path: `env.get(..).cloned()` + `Arc::make_mut` while the
//! owner store and the flat MODULE_GLOBALS mirror still pinned the Arc, so every
//! element store deep-copied the whole array -- O(n) per store, O(n^2) for an
//! arena allocator (`val_alloc` in the pure-Simple core interpreter), which is
//! what pushed `stmt_for_comprehension_no_silent_iteration_cap_spec.spl` past
//! the 900 s runner cap. Also pins the entry-script top-level `g.push(x)` path,
//! whose `"<entry>"` store was never parked and deep-copied on every push.
//! doc/08_tracking/bug/seed_interp_global_array_index_store_cow_quadratic_2026-11-13.md
use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::collections::HashSet;
use std::fs;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

/// The core interpreter's shape: parallel arena arrays in an IMPORTED module,
/// grown by push and then written by index from the same allocator function.
const ARENA: &str = "var kinds: [i64] = []\nvar ints: [i64] = []\n\nfn alloc(n: i64) -> i64:\n    val idx = kinds.len()\n    kinds.push(0)\n    ints.push(0)\n    kinds[idx] = 1\n    ints[idx] = n\n    idx\n\nfn arena_len() -> i64:\n    ints.len()\n\nfn int_at(i: i64) -> i64:\n    ints[i]\n\nfn kind_at(i: i64) -> i64:\n    kinds[i]\n";

fn run_modules(lib: &str, main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("arena.spl"), lib).unwrap();
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

fn program(allocs: usize) -> String {
    let last = allocs - 1;
    [
        "use arena.{alloc, arena_len, int_at, kind_at}",
        "",
        "fn main() -> i32:",
        "    var k = 0",
        &format!("    while k < {allocs}:"),
        "        val _i = alloc(k + 1000)",
        "        k = k + 1",
        &format!("    if arena_len() != {allocs}:"),
        "        return 1",
        &format!("    if int_at({last}) != {last} + 1000:"),
        "        return 2",
        &format!("    if kind_at({last}) != 1:"),
        "        return 3",
        "    if int_at(0) != 1000:",
        "        return 4",
        "    return 0",
        "",
    ]
    .join("\n")
}

fn time_allocs(allocs: usize) -> Duration {
    let start = Instant::now();
    let result = run_modules(ARENA, &program(allocs));
    let elapsed = start.elapsed();
    assert_eq!(
        result,
        Ok(0),
        "arena with {allocs} allocs must run and keep its contents"
    );
    elapsed
}

#[test]
fn global_array_index_store_in_a_function_does_not_deep_copy() {
    perf_counters::set_enabled(true);
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let before_in_place = perf_counters::INDEX_STORE_GLOBAL_IN_PLACE.load(Ordering::Relaxed);
    let before_elems = perf_counters::INDEX_STORE_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    let n = 2_000;
    assert_eq!(run_modules(ARENA, &program(n)), Ok(0));
    let in_place = perf_counters::INDEX_STORE_GLOBAL_IN_PLACE.load(Ordering::Relaxed) - before_in_place;
    let elems = perf_counters::INDEX_STORE_COW_ELEMS_CLONED.load(Ordering::Relaxed) - before_elems;
    eprintln!("[global-index-store] {n} allocs: in-place={in_place} cow-elements-cloned={elems}");
    assert!(
        in_place >= 2 * n as u64,
        "the in-place path must handle every arena store (got {in_place})"
    );
    // Pre-fix: two arrays x n stores x growing length = ~n^2 (~4M) elements.
    assert!(
        elems < 10 * n as u64,
        "global index stores deep-copied {elems} elements for {n} allocs (quadratic)"
    );
}

#[test]
fn global_array_index_store_scales_linearly() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let _ = time_allocs(500);
    let small = time_allocs(4_000);
    let large = time_allocs(16_000);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(0.001);
    eprintln!("[global-index-store] 4000 allocs {small:?}, 16000 allocs {large:?}, ratio {ratio:.2} (linear ~4, quadratic ~16)");
    assert!(
        ratio < 7.0,
        "global array index store from a function is super-linear: x4 allocs cost x{ratio:.1}"
    );
}

#[test]
fn aliased_global_still_copies_on_index_store() {
    // Value semantics: a snapshot taken before the store must not observe it;
    // the global, a callee and the caller must all see it afterwards.
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let lib = "var pool: [i64] = [1, 2, 3]\n\nfn read0() -> i64:\n    pool[0]\n\nfn set0(v: i64):\n    pool[0] = v\n\nfn check() -> i32:\n    val snapshot = pool\n    pool[0] = 99\n    if snapshot[0] != 1:\n        return 1\n    if pool[0] != 99:\n        return 2\n    if read0() != 99:\n        return 3\n    set0(5)\n    if pool[0] != 5:\n        return 4\n    pool[1] = read0() + 10\n    if pool[1] != 15:\n        return 5\n    pool[4] = 7\n    if pool.len() != 5:\n        return 6\n    0\n\nfn pool_at(i: i64) -> i64:\n    pool[i]\n";
    let main = "use arena.{check, pool_at}\n\nfn main() -> i32:\n    val r = check()\n    if r != 0:\n        return r\n    if pool_at(1) != 15:\n        return 7\n    if pool_at(4) != 7:\n        return 8\n    0\n";
    assert_eq!(run_modules(lib, main), Ok(0));
}

#[test]
fn local_shadow_of_a_global_is_not_written_through() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let lib = "var pool: [i64] = [1, 2]\n\nfn shadow() -> i64:\n    var pool: [i64] = [7, 8]\n    pool[0] = 70\n    pool[0]\n\nfn pool_at(i: i64) -> i64:\n    pool[i]\n";
    let main = "use arena.{shadow, pool_at}\n\nfn main() -> i32:\n    if shadow() != 70:\n        return 1\n    if pool_at(0) != 1:\n        return 2\n    0\n";
    assert_eq!(run_modules(lib, main), Ok(0));
}

#[test]
fn entry_top_level_push_does_not_deep_copy() {
    // The entry script's top-level code has no executing module; its globals
    // live in the "<entry>" store, which release_global_aliases must park.
    perf_counters::set_enabled(true);
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let n = 2_000;
    let main = format!(
        "var g: [i64] = []\nvar i = 0\nwhile i < {n}:\n    g.push(i)\n    i = i + 1\n\nfn main() -> i32:\n    if g.len() != {n}:\n        return 1\n    if g[{last}] != {last}:\n        return 2\n    0\n",
        last = n - 1
    );
    let before = perf_counters::ARR_MUT_COW_ELEMS_CLONED.load(Ordering::Relaxed);
    assert_eq!(run_modules(ARENA, &main), Ok(0));
    let elems = perf_counters::ARR_MUT_COW_ELEMS_CLONED.load(Ordering::Relaxed) - before;
    eprintln!("[entry-push] {n} pushes: cow-elements-cloned={elems}");
    assert!(
        elems < 10 * n as u64,
        "entry top-level pushes deep-copied {elems} elements for {n} pushes (quadratic)"
    );
}
