// A match EXPRESSION must not make every later statement in the frame cost
// O(module globals).
//
// Until 2026-08-22 the match-expression arm wrote its env back to the frame
// by iterating every VISIBLE entry of the arm env (module globals included)
// and `insert`ing each one that the frame could see. The frame's overlay
// therefore ended up holding every module global, all marked dirty, and every
// later call from the frame re-published all of them
// (`sync_owned_captured_globals` walks the overlay). In the HIR lowering
// (hundreds of visible globals) that was ~10 ms per statement after a
// `val kind = match ...:` line. The write-back is now dirty-only
// (`copy_back_block_writes`), exactly like the if-expression path.
//
// Ratio-based so it holds on a loaded shared box: pre-fix the match form was
// 5-50x the hoisted form depending on global count; post-fix within noise.
// doc/08_tracking/bug/seed_match_expression_return_arm_statement_cost_cliff_2026-08-22.md

use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use std::time::{Duration, Instant};
use tempfile::tempdir;

const HIGH_LIMIT: u64 = 4_000_000_000;

/// `<tmp>/src/pkg/{lib,main}.spl`: the function under test MUST live in an
/// imported module, since only module functions are owner-tagged and take
/// the owner-scoped global publish path on call return.
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

const POST_STATEMENTS: &str = concat!(
    "    var acc = 0\n",
    "    for i in 0..3:\n",
    "        acc = acc + noop(i)\n",
    "    for i in 0..3:\n",
    "        acc = acc + noop(i)\n",
    "    for i in 0..3:\n",
    "        acc = acc + noop(i)\n",
    "    return acc + kind\n",
);

/// `globals` module-level vars, then `work(k)`: either a match EXPRESSION with
/// two returning arms (the shape under test) or the same logic with the early
/// exits hoisted. Both are followed by the identical post-match statements.
fn program(globals: usize, use_match: bool, calls: usize) -> (String, String) {
    let mut lib = String::from("fn noop(x: i64) -> i64:\n    return x + 1\n");
    for i in 0..globals {
        lib.push_str(&format!("var g{i} = [{i}, {i}]\n"));
    }
    lib.push_str("\nfn work(k: i64) -> i64:\n");
    if use_match {
        lib.push_str("    val kind = match k:\n        case 1: return -1\n        case 2: return -2\n        case _: k\n");
    } else {
        lib.push_str("    if k == 1: return -1\n    if k == 2: return -2\n    val kind = k\n");
    }
    lib.push_str(POST_STATEMENTS);
    let main = format!(
        "use pkg.lib (work)\n\nfn main() -> i32:\n    var i = 0\n    var s = 0\n    while i < {calls}:\n        s = s + work(5)\n        i = i + 1\n    if s != {calls} * 23:\n        return 1\n    return 0\n"
    );
    (lib, main)
}

fn time_form(globals: usize, use_match: bool, calls: usize) -> Duration {
    let (lib, main) = program(globals, use_match, calls);
    let start = Instant::now();
    let result = run_pkg_program(&lib, &main);
    let elapsed = start.elapsed();
    assert_eq!(result, Ok(0), "program ({globals} globals, match={use_match}) must run and compute 23 per call");
    elapsed
}

#[test]
fn statements_after_match_expression_do_not_cost_module_globals() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let _ = time_form(300, true, 20);
    let calls = 200;
    let hoisted = time_form(300, false, calls);
    let matched = time_form(300, true, calls);
    let ratio = matched.as_secs_f64() / hoisted.as_secs_f64().max(0.001);
    eprintln!("[match-cliff] {calls} calls, 300 globals: hoisted {hoisted:?}, match-expr {matched:?}, ratio {ratio:.2}");
    assert!(
        ratio < 3.0,
        "statements after a match expression scale with module globals: hoisted form {hoisted:?} \
         vs match-expression form {matched:?} (ratio {ratio:.1}; dirty-only write-back keeps this near 1)"
    );
}

/// Semantics pinned alongside the perf fix: a returning arm still returns from
/// the enclosing function, and a write to an outer local inside a taken arm
/// still reaches the frame.
#[test]
fn match_expression_returning_arm_and_arm_writes_keep_semantics() {
    simple_compiler::set_execution_limit(HIGH_LIMIT);
    let lib = "var total = 0\n\n\
        fn classify(k: i64) -> i64:\n    var seen = 0\n    val kind = match k:\n        case 1: return -1\n        case _:\n            seen = k * 10\n            total = total + 1\n            k\n    return kind + seen\n";
    let main = "use pkg.lib (classify, total)\n\nfn main() -> i32:\n    if classify(1) != -1:\n        return 1\n    if classify(3) != 33:\n        return 2\n    if total != 1:\n        return 3\n    return 0\n";
    assert_eq!(run_pkg_program(lib, main), Ok(0));
}
