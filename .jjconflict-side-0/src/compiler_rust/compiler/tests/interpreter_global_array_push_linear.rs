// `g.push(x)` on a MODULE-GLOBAL array from inside a function must be O(1)
// amortised, not O(len).
//
// Until 2026-08-22 every mutation of a module-global array from a helper fn
// (`expr_tag.push(tag)` in `expr_alloc`, the flat-AST side tables) deep-copied
// the whole backing Vec: the receiver Arc was aliased by MODULE_GLOBALS, the
// owner's live store and the frame's store snapshot, so `Arc::make_mut` cloned
// on every call (SIMPLE_PERF_COUNTERS: ARR_MUT_COW_CLONES == ARR_MUT_CALLS,
// 4.5M elements copied for N=3000). Measured: 20k pushes 5.0 s, 80k pushes
// 143 s (quadratic); the same loop on a LOCAL array is 0.65 s at 80k.
// The in-place path now parks the stores' handles and drops the snapshot for
// the duration of the write, then re-publishes the mutated Arc.
//
// Ratio-based: 4x the pushes must cost well under 8x (pre-fix 16-20x).
// doc/08_tracking/bug/seed_global_array_push_quadratic_2026-08-22.md

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

fn run_pkg_program(lib: &str, main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(pkg.join("lib.spl"), lib).unwrap();
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

const LIB: &str = "var g_tag: [i64] = []\nvar g_s: [text] = []\n\nfn alloc(t: i64) -> i64:\n    val idx = g_tag.len()\n    g_tag.push(t)\n    g_s.push(\"\")\n    idx\n\nfn fill(n: i64) -> i64:\n    var i = 0\n    while i < n:\n        alloc(i)\n        i = i + 1\n    g_tag.len()\n";

fn time_fill(n: usize) -> Duration {
    let main =
        format!("use pkg.lib (fill)\n\nfn main() -> i32:\n    if fill({n}) != {n}:\n        return 1\n    return 0\n");
    let start = Instant::now();
    let result = run_pkg_program(LIB, &main);
    let elapsed = start.elapsed();
    assert_eq!(result, Ok(0), "fill({n}) must push exactly n elements");
    elapsed
}

#[test]
fn module_global_array_push_from_helper_fn_is_linear() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let _ = time_fill(500); // warm
    let small = time_fill(2_000);
    let large = time_fill(8_000);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(0.001);
    eprintln!("[global-push] 2k {small:?}, 8k {large:?}, ratio {ratio:.2}");
    assert!(
        ratio < 8.0,
        "4x pushes cost {ratio:.1}x — global array push is copying the Vec per call again"
    );
}

#[test]
fn module_global_array_push_keeps_value_semantics() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    // An alias taken BEFORE a push must not observe the push (copy-on-write),
    // and the global must see every push across helper-fn calls.
    let lib = "var g: [i64] = []\n\nfn add(x: i64):\n    g.push(x)\n\nfn snapshot() -> [i64]:\n    g\n";
    let main = "use pkg.lib (add, snapshot, g)\n\nfn main() -> i32:\n    add(1)\n    val before = snapshot()\n    add(2)\n    add(3)\n    if before.len() != 1:\n        return 1\n    if g.len() != 3:\n        return 2\n    if g[2] != 3:\n        return 3\n    return 0\n";
    assert_eq!(run_pkg_program(lib, main), Ok(0));
}
