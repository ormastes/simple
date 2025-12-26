#![allow(unused_imports, deprecated)]

use assert_cmd::Command;
use predicates::prelude::PredicateBooleanExt;
use predicates::str::contains;
use simple_driver::dependency_cache::{analyze_source_str, BuildCache, DepInfo};
use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};
use simple_driver::runner::Runner;
use simple_runtime::gc::GcRuntime;
use simple_term_io::io::term::TermNative;
use std::fs;
use std::sync::{Arc, Mutex};
use tempfile::TempDir;

// Import shared test helpers
mod test_helpers;
use test_helpers::{
    run_expect, run_expect_compile_error, run_expect_compile_error_at, run_expect_error,
    run_expect_interp, run_expect_parity, run_expect_runtime_error,
};

#[test]
fn runner_compiles_and_runs_stub() {
    run_expect("main = 0", 0);
}

/// Test AOT executable mode specifically (all 3 modes: interpreter, JIT, AOT)
#[test]
fn runner_aot_executable_works() {
    use crate::test_helpers::run_expect_all;
    // Simple integer returns work in AOT
    run_expect_all("main = 42", 42);
    run_expect_all("main = 0", 0);
    run_expect_all("main = 100", 100);
    // Simple arithmetic works in AOT
    run_expect_all("main = 1 + 2", 3);
    run_expect_all("main = 10 * 5", 50);
}

#[test]
fn runner_returns_integer_literal_value() {
    run_expect("main = 42", 42);
    run_expect("main = 1", 1);
    run_expect("main = 255", 255);
}

#[test]
fn runner_evaluates_arithmetic_expressions() {
    run_expect("main = 1 + 2", 3);
    run_expect("main = 10 - 3", 7);
    run_expect("main = 6 * 7", 42);
    run_expect("main = 15 / 3", 5);
    run_expect("main = 17 % 5", 2);
    run_expect("main = 2 + 3 * 4", 14);
    run_expect("main = (2 + 3) * 4", 20);
}

#[test]
fn runner_supports_variables() {
    run_expect("let x = 42\nmain = x", 42);
    run_expect("let x = 10\nlet y = 20\nmain = x + y", 30);
    run_expect("let a = 5\nmain = a * a", 25);
    run_expect("let x = 7\nlet y = x + 3\nmain = y", 10);
    run_expect("let a = 2\nlet b = 3\nlet c = 4\nmain = a + b * c", 14);
}

#[test]
fn runner_handles_if_else_and_loops() {
    run_expect(
        r#"
let mut sum = 0
let mut i = 0
while i < 5:
    if i % 2 == 0:
        sum = sum + i
    i = i + 1
main = sum
"#,
        6,
    ); // 0 + 2 + 4
}

#[test]
fn runner_handles_for_loop_and_break_continue() {
    run_expect(
        r#"
let mut sum = 0
for i in range(0, 10):
    if i == 5:
        break
    if i % 2 == 0:
        continue
    sum = sum + i
main = sum
"#,
        4,
    ); // 1 + 3
}

#[test]
fn runner_handles_functions() {
    run_expect(
        r#"
fn add(a: i64, b: i64) -> i64:
    return a + b
main = add(2, 3)
"#,
        5,
    );
}

#[test]
fn runner_handles_class_methods() {
    run_expect(
        r#"
class Point:
    fn value():
        return 7

main = Point.value()
"#,
        7,
    );
}

#[test]
fn runner_supports_unique_new() {
    run_expect("main = new & 21", 21);
}

#[test]
fn runner_supports_gc_off_mode() {
    let runner = Runner::new_no_gc();
    let exit = runner.run_source("main = 7").expect("run ok");
    assert_eq!(exit, 7);
}

#[test]
fn runner_can_use_system_term_lib() {
    let term = TermNative::load().expect("term native loads");
    assert_eq!(term.add(10, 5), Some(15));
    assert_eq!(term.strlen("system"), Some(6));
}

#[test]
fn runner_runs_from_file() {
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("hello.spl");
    std::fs::write(&src_path, "main = 0").unwrap();

    let runner = Runner::new();
    let exit = runner.run_file(&src_path).expect("run from file");
    assert_eq!(exit, 0);

    let smf_path = src_path.with_extension("smf");
    let meta = std::fs::metadata(&smf_path).expect("smf emitted");
    assert!(meta.len() > 0, "smf should not be empty");
}

#[test]
fn dependency_analysis_finds_imports_and_macros() {
    let source = r#"
        import foo/bar
        import baz.spl
        macro MY_MACRO(x: Int) -> (returns result: Int):
            emit result:
                x
        macro other() -> (returns result: Int):
            emit result:
                1
    "#;

    let (deps, macros) = analyze_source_str(std::path::Path::new("main.spl"), source);
    assert!(deps.iter().any(|d| d.ends_with("bar.spl")));
    assert!(deps.iter().any(|d| d.ends_with("baz.spl")));
    assert!(macros.contains(&"MY_MACRO".to_string()));
    assert!(macros.contains(&"other".to_string()));

    let mut cache = BuildCache::default();
    cache.update(DepInfo {
        source: "main.spl".into(),
        output: "main.smf".into(),
        dependencies: deps.clone(),
        macros: macros.clone(),
        mtime: 0,
    });
    let dependents = cache.dependents_of(deps.first().unwrap());
    assert_eq!(dependents.len(), 1);
}

#[test]
fn runner_handles_enums() {
    run_expect(
        r#"
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#,
        1,
    );
}

#[test]
fn runner_handles_structs() {
    run_expect(
        r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#,
        30,
    );
}

#[test]
fn runner_emits_gc_logs_in_verbose_mode() {
    let events = Arc::new(Mutex::new(Vec::new()));
    let logger = {
        let events = events.clone();
        move |event: simple_runtime::gc::GcLogEvent| {
            events.lock().unwrap().push(event.to_string());
        }
    };
    let runner = Runner::with_gc_runtime(GcRuntime::with_logger(logger));
    let exit = runner.run_source("main = 0").expect("run ok");
    assert_eq!(exit, 0);

    let logs = events.lock().unwrap();
    assert!(
        logs.iter().any(|l| l.contains("gc:start reason=post-run")),
        "expected GC start log after run"
    );
    assert!(
        logs.iter().any(|l| l.contains("gc:end reason=post-run")),
        "expected GC end log after run"
    );
}

#[test]
fn cli_flag_emits_gc_logs() {
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("main.spl");
    std::fs::write(&src_path, "main = 0").unwrap();

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("run").arg(&src_path).arg("--gc-log");

    cmd.assert()
        .success()
        .stdout(contains("gc:start").and(contains("gc:end")));

    assert!(src_path.with_extension("smf").exists());
}

#[test]
fn runner_handles_array_literals_and_indexing() {
    run_expect("let arr = [10, 20, 30]\nmain = arr[0]", 10);
    run_expect("let arr = [10, 20, 30]\nmain = arr[1]", 20);
    run_expect("let arr = [10, 20, 30]\nmain = arr[2]", 30);
    run_expect("let arr = [5, 10, 15]\nlet mut i = 1\nmain = arr[i]", 10);
    run_expect("let arr = [100, 200, 300]\nmain = arr[1 + 1]", 300);
    run_expect("let arr = [2, 3, 4]\nmain = arr[0] + arr[1] * arr[2]", 14);
    run_expect(
        r#"
let arr = [1, 2, 3, 4, 5]
let mut sum = 0
let mut i = 0
while i < 5:
    sum = sum + arr[i]
    i = i + 1
main = sum
"#,
        15,
    );
}

#[test]
fn runner_handles_pattern_matching() {
    // Match on integer literals
    run_expect(
        r#"
let x = 2
let mut res = 0
match x:
    1 =>
        res = 10
    2 =>
        res = 20
    _ =>
        res = 0
main = res
"#,
        20,
    );

    // Match with wildcard
    run_expect(
        r#"
let x = 99
let mut res = 0
match x:
    1 =>
        res = 10
    2 =>
        res = 20
    _ =>
        res = 0
main = res
"#,
        0,
    );

    // Match with variable binding
    run_expect(
        r#"
let x = 42
let mut res = 0
match x:
    n =>
        res = n
main = res
"#,
        42,
    );

    // Spec syntax: match arms using `case pattern:` (doc/spec/functions.md)
    run_expect(
        r#"
let x: i32 = 2
match x:
    case 1:
        main = 10
    case 2:
        main = 20
    case _:
        main = 0
"#,
        20,
    );

    // Match on enum variants
    run_expect(
        r#"
enum Status:
    Ok
    Error

let s = Status::Ok
let mut res = 0
match s:
    Status::Ok =>
        res = 1
    Status::Error =>
        res = 0
main = res
"#,
        1,
    );

    // Match on enum with different variant
    run_expect(
        r#"
enum Status:
    Ok
    Error

let s = Status::Error
let mut res = 0
match s:
    Status::Ok =>
        res = 1
    Status::Error =>
        res = 0
main = res
"#,
        0,
    );

    // Match with guard
    run_expect(
        r#"
let x = 10
let mut res = 0
match x:
    n if n > 5 =>
        res = 1
    n if n <= 5 =>
        res = 0
    _ =>
        res = 99
main = res
"#,
        1,
    );
}

/// Regression: CLI should accept spec `case` match arms; currently fails.
#[test]
fn runner_cli_case_match_rejects_spec_syntax() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let x: i32 = 2\nmatch x:\n    case 2:\n        main = 20\n    case _:\n        main = 0",
    );
    cmd.assert().code(20).stdout(contains("20"));
}

/// Regression: CLI rejects `match` even with `=>` syntax (should succeed).
#[test]
fn runner_cli_match_arrow_rejects_basic_syntax() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c")
        .arg("let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0");
    cmd.assert().code(20).stdout(contains("20"));
}

/// Regression: CLI rejects match when run against a source file.
#[test]
fn runner_cli_match_arrow_file_rejects_basic_syntax() {
    let dir = TempDir::new().expect("tempdir");
    let main_path = dir.path().join("main.spl");
    fs::write(
        &main_path,
        "let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0",
    )
    .expect("write main.spl");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg(&main_path);
    cmd.assert().code(20);
}

/// Regression: CLI rejects match guards with spec `case` syntax.
#[test]
fn runner_cli_case_guard_rejects_spec_syntax() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let x: i32 = 3\nmatch x:\n    case n if n > 0:\n        main = 1\n    case _:\n        main = 0",
    );
    cmd.assert().code(1).stdout(contains("1"));
}

/// Regression: mixed match syntax (case + =>) rejected by CLI.
#[test]
fn runner_cli_match_mixed_syntax_rejects() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let x: i32 = 2\nmatch x:\n    case 1:\n        main = 10\n    2 =>\n        main = 20\n    _ =>\n        main = 0",
    );
    cmd.assert().code(20).stdout(contains("20"));
}

/// Regression: match inside function rejected in CLI executable path.
#[test]
fn runner_cli_match_inside_function_rejects() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "fn f(x: i32) -> i32:\n    match x:\n        1 =>\n            return 10\n        _ =>\n            return 0\nmain = f(1)",
    );
    cmd.assert().code(10).stdout(contains("10"));
}

/// Regression: destructuring patterns rejected in CLI executable path.
#[test]
fn runner_cli_match_destructuring_rejects() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let tup: (i32, i32) = (1, 2)\nmatch tup:\n    (a, b) =>\n        main = a + b\n    _ =>\n        main = 0",
    );
    cmd.assert().code(3).stdout(contains("3"));
}

/// Regression: file + import + match rejected in CLI executable path.
#[test]
fn runner_cli_match_in_imported_module_rejects() {
    let dir = TempDir::new().expect("tempdir");
    let lib_path = dir.path().join("lib.spl");
    fs::write(
        &lib_path,
        "pub fn classify(x: i32) -> i32:\n    match x:\n        0 =>\n            return 0\n        _ =>\n            return 1\n",
    )
    .expect("write lib.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, "use lib\nmain = lib::classify(0)").expect("write main.spl");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.current_dir(dir.path());
    cmd.arg(&main_path);
    cmd.assert().code(0);
}

/// Regression: module import via `use` + dot call works in CLI executable path.
#[test]
fn runner_cli_match_in_imported_module_dot_call() {
    let dir = TempDir::new().expect("tempdir");
    let lib_path = dir.path().join("lib.spl");
    fs::write(
        &lib_path,
        "pub fn classify(x: i32) -> i32:\n    match x:\n        0 =>\n            return 0\n        _ =>\n            return 1\n",
    )
    .expect("write lib.spl");
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, "use lib\nmain = lib.classify(0)").expect("write main.spl");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.current_dir(dir.path());
    cmd.arg(&main_path);
    cmd.assert().code(0);
}

/// Regression: array destructuring rejected in CLI executable path.
#[test]
fn runner_cli_array_destructuring_rejects() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let arr: [i32] = [1, 2, 3]\nmatch arr:\n    [a, b, c] =>\n        main = a + b + c\n    _ =>\n        main = 0",
    );
    cmd.assert().code(6).stdout(contains("6"));
}

/// Regression: guard referencing outer binding rejected in CLI executable path.
#[test]
fn runner_cli_guard_outer_binding_rejects() {
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg(
        "let y: i32 = 2\nlet x: i32 = 2\nmatch x:\n    case y if x == y:\n        main = 1\n    _ =>\n        main = 0",
    );
    cmd.assert().code(1).stdout(contains("1"));
}

#[test]
fn runner_handles_pattern_matching_functions() {
    // Match in a function with return (interpreter-only, match not in HIR lowering yet)
    run_expect_interp(
        r#"
fn classify(n: i64) -> i64:
    match n:
        0 =>
            return 0
        1 =>
            return 1
        _ =>
            return 2

main = classify(0) + classify(1) * 10 + classify(99) * 100
"#,
        210,
    );
}

#[test]
fn runner_handles_spawn_expression() {
    run_expect(
        r#"
fn work():
    return 42
let handle = spawn work()
main = 0
"#,
        0,
    );
}

#[test]
fn runner_handles_actor_send_recv_join() {
    // Uses recv/reply/send builtins not yet in native codegen, so interpreter-only
    run_expect_interp(
        r#"
fn worker():
    let msg = recv()
    reply(msg)

let h = spawn worker()
send(h, "ping")
let resp = recv(h)
join(h)
main = if resp == "ping": 0 else: 1
"#,
        0,
    );
}

#[test]
fn runner_handles_tuples() {
    run_expect("let t = (10, 20, 30)\nmain = t[0]", 10);
    run_expect("let t = (10, 20, 30)\nmain = t[1]", 20);
    run_expect("let t = (10, 20, 30)\nmain = t[2]", 30);
    run_expect("let t = (2, 3, 4)\nmain = t[0] + t[1] * t[2]", 14);
    run_expect(
        r#"
let point = (5, 10)
let x = point[0]
let y = point[1]
main = x + y
"#,
        15,
    );
    run_expect("let t = ()\nmain = 42", 42);
}

#[test]
fn runner_handles_option_type() {
    // Test Some variant with value
    run_expect(
        r#"
enum Option:
    Some(i64)
    None

let x = Option::Some(42)
let mut res = 0
match x:
    Option::Some(v) =>
        res = v
    Option::None =>
        res = 0
main = res
"#,
        42,
    );

    // Test None variant
    run_expect(
        r#"
enum Option:
    Some(i64)
    None

let x = Option::None
let mut res = 0
match x:
    Option::Some(v) =>
        res = v
    Option::None =>
        res = 99
main = res
"#,
        99,
    );
}

#[test]
fn runner_handles_option_type_functions() {
    // Test Option in function (interpreter-only, match not in HIR lowering yet)
    run_expect_interp(
        r#"
enum Option:
    Some(i64)
    None

fn get_value(opt: Option) -> i64:
    match opt:
        Option::Some(v) =>
            return v
        Option::None =>
            return 0

let a = Option::Some(10)
let b = Option::None
main = get_value(a) + get_value(b)
"#,
        10,
    );
}

#[test]
fn runner_handles_dictionary_types() {
    run_expect(
        r#"let d = {"a": 10, "b": 20, "c": 30}
main = d["a"]"#,
        10,
    );
    run_expect(
        r#"let d = {1: 100, 2: 200, 3: 300}
main = d[2]"#,
        200,
    );
    run_expect(
        r#"let d = {"x": 5, "y": 7}
main = d["x"] + d["y"]"#,
        12,
    );
    run_expect(
        r#"let d = {"first": 1, "second": 2}
let key = "second"
main = d[key]"#,
        2,
    );
    run_expect("let d = {}\nmain = 42", 42);
}

// =============================================================================
// Pointer tests (tests both interpreter and JIT/compiled paths)
// =============================================================================

#[test]
fn runner_handles_unique_pointer_allocation() {
    // Test unique pointer with & syntax
    run_expect_interp("let p = new & 42\nmain = p", 42);
}

#[test]
fn runner_handles_shared_pointer_allocation() {
    // Test shared pointer with * syntax
    run_expect_interp("let p = new * 42\nmain = p", 42);
}

#[test]
fn runner_handles_pointer_arithmetic() {
    // Test arithmetic with pointers (auto-deref)
    run_expect_interp(
        r#"
let a = new * 10
let b = new * 5
main = a + b
"#,
        15,
    );
}

#[test]
fn runner_handles_multiple_shared_refs() {
    // Test multiple references to same shared value
    run_expect_interp(
        r#"
let a = new * 42
let b = a
main = a + b
"#,
        84,
    );
}
