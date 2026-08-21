// Per-call environment setup in the tree-walk interpreter must be O(args),
// not O(module globals).
//
// Until 2026-08-21 every call into a module function materialized the callee
// env from EVERY global the module could see (owner globals + imports +
// module env), with a per-owner template cache that any global write
// invalidated. A function that writes one global therefore paid O(globals)
// per call: `lint src/compiler/80.driver/driver_types.spl` never finished in
// 150 s and reached 2.1 GB RSS. The env now resolves globals through a
// parent-pointer scope (`GlobalScope` in value.rs), so the SAME call sequence
// costs the same whether the module declares 200 globals or 4,000.
//
// The assertion is a ratio, not an absolute time, so it holds on a loaded
// shared box: pre-fix the 4,000-global run was ~20x the 200-global run;
// post-fix they are within noise of each other.
// doc/08_tracking/bug/seed_interpreter_env_rebuild_per_call_o_globals_2026-08-21.md

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

/// `<tmp>/src/pkg/{lib,main}.spl`, the layout the loader resolves
/// `use pkg.lib (...)` against (see tests/import_cycle_detection.rs). The
/// function under test MUST live in an imported module: only module functions
/// are owner-tagged and take the owner-scoped env path; a function in the entry
/// file itself resolves globals through the flat fallback and never paid
/// O(globals) per call.
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

/// A module with `globals` module-level `var`s plus one its function writes,
/// and an entry that calls that function `calls` times.
fn program(globals: usize, calls: usize) -> (String, String) {
    let mut lib = String::new();
    for i in 0..globals {
        lib.push_str(&format!("var g{i} = {i}\n"));
    }
    lib.push_str("var counter = 0\n\nfn bump(i: i64) -> i64:\n    counter = counter + i\n    return counter\n");
    let main = format!(
        "use pkg.lib (bump)\n\nfn main() -> i32:\n    var i = 0\n    while i < {calls}:\n        bump(1)\n        i = i + 1\n    return 0\n"
    );
    (lib, main)
}

fn time_calls(globals: usize, calls: usize) -> Duration {
    let (lib, main) = program(globals, calls);
    let start = Instant::now();
    let result = run_pkg_program(&lib, &main);
    let elapsed = start.elapsed();
    assert_eq!(result, Ok(0), "program with {globals} globals / {calls} calls must run");
    elapsed
}

#[test]
fn per_call_env_setup_does_not_scale_with_module_global_count() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    // Warm the loader and allocator so the first timed run is not paying
    // one-off costs.
    let _ = time_calls(200, 1_000);
    let calls = 20_000;
    let small = time_calls(200, calls);
    let large = time_calls(4_000, calls);
    let ratio = large.as_secs_f64() / small.as_secs_f64().max(0.001);
    eprintln!("[env-o-args] {calls} calls: 200 globals {small:?}, 4000 globals {large:?}, ratio {ratio:.2}");
    assert!(
        ratio < 3.0,
        "per-call cost scales with module global count: {calls} calls took {small:?} with 200 globals \
         but {large:?} with 4000 globals (ratio {ratio:.1}; O(args) setup keeps this near 1)"
    );
}

/// A frame's write to its OWN module global must be visible, DURING that
/// frame, to a function of another module that imports the global. The
/// publish at call entry runs with the caller's store snapshot released (so
/// the store maps are uniquely owned and the write is in place); an
/// intermediate build answered "not a global" for the owner's own names while
/// released and silently skipped that publish. A same-module reader would not
/// notice (it resolves through the flat fallback); a cross-module reader goes
/// through the owner's live store and saw a one-append-stale arena — stage-1
/// died with `array index out of bounds: index is 742 but length is 742`.
/// The reader is handed in as a function value to avoid an import cycle.
#[test]
fn caller_write_to_own_module_global_is_visible_to_other_module_during_frame() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(
        pkg.join("writer.spl"),
        "var log: [i64] = []\n\n\
         fn append_then_ask(v: i64, ask: fn() -> i64) -> i64:\n    log = log + [v]\n    return ask()\n",
    )
    .unwrap();
    fs::write(
        pkg.join("reader.spl"),
        "use pkg.writer (log)\n\nfn peek_len() -> i64:\n    return log.len()\n",
    )
    .unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(
        &main_path,
        "use pkg.writer (append_then_ask)\nuse pkg.reader (peek_len)\n\n\
         fn main() -> i32:\n    if append_then_ask(7, peek_len) != 1:\n        return 1\n    if append_then_ask(8, peek_len) != 2:\n        return 2\n    return 0\n",
    )
    .unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items).map_err(|e| format!("{e:?}"));
    interpreter::set_current_file(None);
    assert_eq!(result, Ok(0), "the other module must see the caller's append (1, then 2 elements)");
}
