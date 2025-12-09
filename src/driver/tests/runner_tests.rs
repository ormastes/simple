use simple_driver::runner::Runner;
use simple_driver::dependency_cache::{analyze_source_str, BuildCache, DepInfo};
use simple_term_io::io::term::TermNative;
use simple_runtime::gc::GcRuntime;
use std::sync::{Arc, Mutex};
use assert_cmd::Command;
use predicates::prelude::PredicateBooleanExt;
use predicates::str::contains;

#[test]
fn runner_compiles_and_runs_stub() {
    let runner = Runner::new();
    let exit = runner.run_source("main = 0").expect("run ok");
    assert_eq!(exit, 0);
}

#[test]
fn runner_returns_integer_literal_value() {
    let runner = Runner::new();

    // Test that main = 42 actually returns 42, not 0
    let exit = runner.run_source("main = 42").expect("run ok");
    assert_eq!(exit, 42, "main = 42 should return 42");

    // Test other values
    let exit = runner.run_source("main = 1").expect("run ok");
    assert_eq!(exit, 1, "main = 1 should return 1");

    let exit = runner.run_source("main = 255").expect("run ok");
    assert_eq!(exit, 255, "main = 255 should return 255");
}

#[test]
fn runner_evaluates_arithmetic_expressions() {
    let runner = Runner::new();

    // Addition
    let exit = runner.run_source("main = 1 + 2").expect("run ok");
    assert_eq!(exit, 3, "1 + 2 should equal 3");

    // Subtraction
    let exit = runner.run_source("main = 10 - 3").expect("run ok");
    assert_eq!(exit, 7, "10 - 3 should equal 7");

    // Multiplication
    let exit = runner.run_source("main = 6 * 7").expect("run ok");
    assert_eq!(exit, 42, "6 * 7 should equal 42");

    // Division
    let exit = runner.run_source("main = 15 / 3").expect("run ok");
    assert_eq!(exit, 5, "15 / 3 should equal 5");

    // Modulo
    let exit = runner.run_source("main = 17 % 5").expect("run ok");
    assert_eq!(exit, 2, "17 % 5 should equal 2");

    // Complex expression with precedence
    let exit = runner.run_source("main = 2 + 3 * 4").expect("run ok");
    assert_eq!(exit, 14, "2 + 3 * 4 should equal 14 (not 20)");

    // Parentheses
    let exit = runner.run_source("main = (2 + 3) * 4").expect("run ok");
    assert_eq!(exit, 20, "(2 + 3) * 4 should equal 20");
}

#[test]
fn runner_supports_variables() {
    let runner = Runner::new();

    // Simple variable
    let exit = runner.run_source("let x = 42\nmain = x").expect("run ok");
    assert_eq!(exit, 42, "let x = 42; main = x should return 42");

    // Two variables
    let exit = runner.run_source("let x = 10\nlet y = 20\nmain = x + y").expect("run ok");
    assert_eq!(exit, 30, "x + y should return 30");

    // Variable in expression
    let exit = runner.run_source("let a = 5\nmain = a * a").expect("run ok");
    assert_eq!(exit, 25, "a * a should return 25");

    // Variable referencing another variable
    let exit = runner.run_source("let x = 7\nlet y = x + 3\nmain = y").expect("run ok");
    assert_eq!(exit, 10, "y = x + 3 should be 10");

    // Multiple variables in complex expression
    let exit = runner.run_source("let a = 2\nlet b = 3\nlet c = 4\nmain = a + b * c").expect("run ok");
    assert_eq!(exit, 14, "a + b * c should be 14");
}

#[test]
fn runner_handles_if_else_and_loops() {
    let src = r#"
let mut sum = 0
let mut i = 0
while i < 5:
    if i % 2 == 0:
        sum = sum + i
    i = i + 1
main = sum
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 6); // 0 + 2 + 4
}

#[test]
fn runner_handles_for_loop_and_break_continue() {
    let src = r#"
let mut sum = 0
for i in range(0, 10):
    if i == 5:
        break
    if i % 2 == 0:
        continue
    sum = sum + i
main = sum
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 4); // 1 + 3
}

#[test]
fn runner_handles_functions() {
    let src = r#"
fn add(a, b):
    return a + b
main = add(2, 3)
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 5);
}

#[test]
fn runner_handles_class_methods() {
    let src = r#"
class Point:
    fn value():
        return 7

main = Point.value()
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 7);
}

#[test]
fn runner_supports_unique_new() {
    let runner = Runner::new();
    let exit = runner.run_source("main = new & 21").expect("run ok");
    assert_eq!(exit, 21);
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
        macro MY_MACRO(x) = x
        macro other = 1
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
    let src = r#"
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 1);
}

#[test]
fn runner_handles_structs() {
    let src = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let runner = Runner::new();
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 30);
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

    let mut cmd = Command::cargo_bin("simple-driver").expect("binary exists");
    cmd.arg("run").arg(&src_path).arg("--gc-log");

    cmd.assert()
        .success()
        .stdout(contains("gc:start").and(contains("gc:end")));

    assert!(src_path.with_extension("smf").exists());
}

#[test]
fn runner_handles_array_literals_and_indexing() {
    let runner = Runner::new();

    // Simple array index access
    let exit = runner.run_source("let arr = [10, 20, 30]\nmain = arr[0]").expect("run ok");
    assert_eq!(exit, 10, "arr[0] should return 10");

    let exit = runner.run_source("let arr = [10, 20, 30]\nmain = arr[1]").expect("run ok");
    assert_eq!(exit, 20, "arr[1] should return 20");

    let exit = runner.run_source("let arr = [10, 20, 30]\nmain = arr[2]").expect("run ok");
    assert_eq!(exit, 30, "arr[2] should return 30");

    // Index with variable
    let exit = runner.run_source("let arr = [5, 10, 15]\nlet mut i = 1\nmain = arr[i]").expect("run ok");
    assert_eq!(exit, 10, "arr[i] where i=1 should return 10");

    // Index with expression
    let exit = runner.run_source("let arr = [100, 200, 300]\nmain = arr[1 + 1]").expect("run ok");
    assert_eq!(exit, 300, "arr[1+1] should return 300");

    // Array element in arithmetic
    let exit = runner.run_source("let arr = [2, 3, 4]\nmain = arr[0] + arr[1] * arr[2]").expect("run ok");
    assert_eq!(exit, 14, "arr[0] + arr[1] * arr[2] = 2 + 3*4 = 14");

    // Nested array access in loop
    let src = r#"
let arr = [1, 2, 3, 4, 5]
let mut sum = 0
let mut i = 0
while i < 5:
    sum = sum + arr[i]
    i = i + 1
main = sum
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 15, "sum of [1,2,3,4,5] should be 15");
}

#[test]
fn runner_handles_pattern_matching() {
    let runner = Runner::new();

    // Match on integer literals (using block syntax)
let src = r#"
let x = 2
let mut result = 0
match x:
    1 =>
        result = 10
    2 =>
        result = 20
    _ =>
        result = 0
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 20, "match x=2 should return 20");

    // Match with wildcard
let src = r#"
let x = 99
let mut result = 0
match x:
    1 =>
        result = 10
    2 =>
        result = 20
    _ =>
        result = 0
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 0, "match x=99 should hit wildcard and return 0");

    // Match with variable binding
let src = r#"
let x = 42
let mut result = 0
match x:
    n =>
        result = n
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 42, "match with binding should capture value");

    // Match on enum variants
let src = r#"
enum Status:
    Ok
    Error

let s = Status::Ok
let mut result = 0
match s:
    Status::Ok =>
        result = 1
    Status::Error =>
        result = 0
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 1, "match on Status::Ok should return 1");

    // Match on enum with different variant
let src = r#"
enum Status:
    Ok
    Error

let s = Status::Error
let mut result = 0
match s:
    Status::Ok =>
        result = 1
    Status::Error =>
        result = 0
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 0, "match on Status::Error should return 0");

    // Match with guard
let src = r#"
let x = 10
let mut result = 0
match x:
    n if n > 5 =>
        result = 1
    n if n <= 5 =>
        result = 0
    _ =>
        result = 99
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 1, "match with guard n>5 should return 1");

    // Match in a function with return
    let src = r#"
fn classify(n):
    match n:
        0 =>
            return 0
        1 =>
            return 1
        _ =>
            return 2

main = classify(0) + classify(1) * 10 + classify(99) * 100
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 210, "classify(0)=0, classify(1)=1, classify(99)=2 -> 0+10+200=210");
}

#[test]
fn runner_handles_spawn_expression() {
    let runner = Runner::new();
    // spawn is fire-and-forget; we just assert it doesn't crash.
    // The spawned actor returns a handle, so we store it and return a fixed value.
    let src = r#"
fn work():
    return 42
let handle = spawn work()
main = 0
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 0);
}

#[test]
fn runner_handles_actor_send_recv_join() {
    let runner = Runner::new();
    let src = r#"
fn worker():
    let msg = recv()
    reply(msg)

let h = spawn worker()
send(h, "ping")
let resp = recv(h)
join(h)
main = if resp == "ping": 0 else: 1
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 0, "actor roundtrip should succeed");
}

#[test]
fn runner_handles_tuples() {
    let runner = Runner::new();

    // Simple tuple creation and indexing
    let exit = runner.run_source("let t = (10, 20, 30)\nmain = t[0]").expect("run ok");
    assert_eq!(exit, 10, "tuple[0] should be 10");

    let exit = runner.run_source("let t = (10, 20, 30)\nmain = t[1]").expect("run ok");
    assert_eq!(exit, 20, "tuple[1] should be 20");

    let exit = runner.run_source("let t = (10, 20, 30)\nmain = t[2]").expect("run ok");
    assert_eq!(exit, 30, "tuple[2] should be 30");

    // Tuple arithmetic
    let exit = runner.run_source("let t = (2, 3, 4)\nmain = t[0] + t[1] * t[2]").expect("run ok");
    assert_eq!(exit, 14, "2 + 3*4 = 14");

    // Nested tuple usage
    let src = r#"
let point = (5, 10)
let x = point[0]
let y = point[1]
main = x + y
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 15, "5 + 10 = 15");

    // Empty tuple
    let exit = runner.run_source("let t = ()\nmain = 42").expect("run ok");
    assert_eq!(exit, 42, "empty tuple should work");
}

#[test]
fn runner_handles_option_type() {
    let runner = Runner::new();

    // Using user-defined Option enum (since no built-in generics yet)
    // Test Some variant with value
    let src = r#"
enum Option:
    Some(i64)
    None

let x = Option::Some(42)
let mut result = 0
match x:
    Option::Some(v) =>
        result = v
    Option::None =>
        result = 0
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 42, "Some(42) should unwrap to 42");

    // Test None variant
    let src = r#"
enum Option:
    Some(i64)
    None

let x = Option::None
let mut result = 0
match x:
    Option::Some(v) =>
        result = v
    Option::None =>
        result = 99
main = result
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 99, "None should match None arm");

    // Test Option in function
    let src = r#"
enum Option:
    Some(i64)
    None

fn get_value(opt):
    match opt:
        Option::Some(v) =>
            return v
        Option::None =>
            return 0

let a = Option::Some(10)
let b = Option::None
main = get_value(a) + get_value(b)
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 10, "get_value(Some(10)) + get_value(None) = 10 + 0 = 10");
}

#[test]
fn runner_handles_dictionary_types() {
    let runner = Runner::new();

    // Simple dict with string keys
    let src = r#"
let d = {"a": 10, "b": 20, "c": 30}
main = d["a"]
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 10, "d['a'] should be 10");

    // Dict with integer keys
    let src = r#"
let d = {1: 100, 2: 200, 3: 300}
main = d[2]
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 200, "d[2] should be 200");

    // Dict value arithmetic
    let src = r#"
let d = {"x": 5, "y": 7}
main = d["x"] + d["y"]
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 12, "d['x'] + d['y'] = 5 + 7 = 12");

    // Dict with variable key lookup
    let src = r#"
let d = {"first": 1, "second": 2}
let key = "second"
main = d[key]
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 2, "d[key] where key='second' should be 2");

    // Empty dict
    let exit = runner.run_source("let d = {}\nmain = 42").expect("run ok");
    assert_eq!(exit, 42, "empty dict should work");
}

#[test]
fn runner_handles_mutability_control() {
    let runner = Runner::new();

    // let is immutable by default; reassignment without mut should fail
    let src = r#"
let x = 10
x = 20
main = x
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "immutable let should reject reassignment");

    // Mutable binding with let mut allows reassignment
    let src = r#"
let mut x = 10
x = 20
main = x
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 20, "let mut variables can be reassigned");

    // Bare assignment creates mutable variable (Python-like)
    let src = r#"
y = 10
y = 30
main = y
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 30, "bare assignment creates mutable variable");

    // Variables in loop (no mut needed)
    let src = r#"
sum = 0
i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 10, "sum of 0+1+2+3+4 = 10");

    // const is immutable (cannot be reassigned)
    let src = r#"
const x = 10
x = 20
main = x
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "const reassignment should fail");
    let err = result.unwrap_err();
    assert!(err.contains("immutable") || err.contains("cannot assign"), "error should mention immutability");
}

#[test]
fn runner_handles_static_const_declarations() {
    let runner = Runner::new();

    // Simple const declaration
    let src = r#"
const MAX = 100
main = MAX
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 100, "const MAX should be 100");

    // Const with arithmetic
    let src = r#"
const BASE = 10
const MULTIPLIER = 5
main = BASE * MULTIPLIER
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 50, "BASE * MULTIPLIER = 10 * 5 = 50");

    // Const cannot be reassigned (should error)
    let src = r#"
const X = 10
X = 20
main = X
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "const reassignment should fail");

    // Static variable (immutable by default)
    let src = r#"
static counter = 42
main = counter
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 42, "static counter should be 42");

    // Static mut variable can be reassigned
    let src = r#"
static mut counter = 0
counter = counter + 1
counter = counter + 1
main = counter
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 2, "static mut counter should be 2 after two increments");

    // Static (non-mut) cannot be reassigned (should error)
    let src = r#"
static counter = 10
counter = 20
main = counter
"#;
    let result = runner.run_source(src);
    assert!(result.is_err(), "static (non-mut) reassignment should fail");

    // Const with type annotation
    let src = r#"
const SIZE: i64 = 256
main = SIZE
"#;
    let exit = runner.run_source(src).expect("run ok");
    assert_eq!(exit, 256, "const SIZE should be 256");
}
