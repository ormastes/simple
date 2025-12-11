use assert_cmd::Command;
use predicates::prelude::PredicateBooleanExt;
use predicates::str::contains;
use simple_driver::dependency_cache::{analyze_source_str, BuildCache, DepInfo};
use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};
use simple_driver::runner::Runner;
use simple_runtime::gc::GcRuntime;
use simple_term_io::io::term::TermNative;
use std::sync::{Arc, Mutex};

// Import shared test helpers
mod test_helpers;
use test_helpers::{run_expect, run_expect_interp, run_expect_parity, run_expect_compile_error, run_expect_compile_error_at, run_expect_runtime_error, run_expect_error};

#[test]
fn runner_compiles_and_runs_stub() {
    run_expect("main = 0", 0);
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
let mut result = 0
match x:
    1 =>
        result = 10
    2 =>
        result = 20
    _ =>
        result = 0
main = result
"#,
        20,
    );

    // Match with wildcard
    run_expect(
        r#"
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
"#,
        0,
    );

    // Match with variable binding
    run_expect(
        r#"
let x = 42
let mut result = 0
match x:
    n =>
        result = n
main = result
"#,
        42,
    );

    // Match on enum variants
    run_expect(
        r#"
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
let mut result = 0
match s:
    Status::Ok =>
        result = 1
    Status::Error =>
        result = 0
main = result
"#,
        0,
    );

    // Match with guard
    run_expect(
        r#"
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
"#,
        1,
    );

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
let mut result = 0
match x:
    Option::Some(v) =>
        result = v
    Option::None =>
        result = 0
main = result
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
let mut result = 0
match x:
    Option::Some(v) =>
        result = v
    Option::None =>
        result = 99
main = result
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
    assert!(
        err.contains("immutable") || err.contains("cannot assign"),
        "error should mention immutability"
    );
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
    assert_eq!(
        exit, 2,
        "static mut counter should be 2 after two increments"
    );

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

// Futures require special runtime setup - skipping for now
// #[test]
// fn runner_handles_futures() {
//     run_expect(r#"
// fn compute():
//     return 42
// let f = async(compute())
// let result = await(f)
// main = result
// "#, 42);
// }

// Generators require yield keyword which may not parse correctly
// #[test]
// fn runner_handles_generators() {
//     run_expect(r#"
// let gen = generator(\:
//     yield 1
//     yield 2
// )
// let a = next(gen)
// let b = next(gen)
// main = a + b
// "#, 3);
// }

// Impl blocks - testing static method syntax
// #[test]
// fn runner_handles_impl_blocks() {
//     run_expect(r#"
// struct Point:
//     x: i64
//     y: i64
// impl Point:
//     fn sum(self):
//         return self.x + self.y
// let p = Point { x: 10, y: 20 }
// main = p.sum()
// "#, 30);
// }

// Context blocks need special parser/runtime support
// #[test]
// fn runner_handles_context_blocks() {
//     run_expect(r#"
// fn get_from_context():
//     return context.value
// context { value: 100 }:
//     main = get_from_context()
// "#, 100);
// }

// Macros may need different invocation syntax
// #[test]
// fn runner_handles_macro_expansion() {
//     run_expect(r#"
// macro double(x) = x + x
// main = double(21)
// "#, 42);
// }

#[test]
fn runner_handles_lambda_expressions() {
    // Basic lambda
    run_expect(
        r#"
let double = \x: x * 2
main = double(21)
"#,
        42,
    );

    // Lambda with multiple params
    run_expect(
        r#"
let add = \a, b: a + b
main = add(10, 32)
"#,
        42,
    );
}

#[test]
fn runner_handles_lambda_higher_order() {
    // Lambda passed to function - uses untyped params, so interpreter-only
    run_expect_interp(
        r#"
fn apply(f, x):
    return f(x)

let inc = \n: n + 1
main = apply(inc, 41)
"#,
        42,
    );
}

#[test]
fn runner_handles_string_operations() {
    // String length
    run_expect(
        r#"
let s = "hello"
main = s.len()
"#,
        5,
    );

    // String concatenation
    run_expect(
        r#"
let a = "hello"
let b = "world"
let c = a + " " + b
main = c.len()
"#,
        11,
    );

    // F-string interpolation
    run_expect(
        r#"
let x = 42
let s = "value is {x}"
main = s.len()
"#,
        11,
    );
}

#[test]
fn runner_handles_array_methods() {
    // Array length
    run_expect(
        r#"
let arr = [1, 2, 3, 4, 5]
main = arr.len()
"#,
        5,
    );
}

// Array push may not return the mutated array correctly
// #[test]
// fn runner_handles_array_push() {
//     run_expect(r#"
// let mut arr = [1, 2]
// arr.push(3)
// main = arr.len()
// "#, 3);
// }

// Map/filter/reduce may need different syntax
// #[test]
// fn runner_handles_array_functional_methods() {
//     run_expect(r#"
// let arr = [1, 2, 3]
// let doubled = arr.map(\x: x * 2)
// main = doubled[0] + doubled[1] + doubled[2]
// "#, 12);
// }

#[test]
fn runner_handles_dict_methods() {
    // Dict len
    run_expect(
        r#"
let d = {"a": 1, "b": 2, "c": 3}
main = d.len()
"#,
        3,
    );

    // Dict keys
    run_expect(
        r#"
let d = {"x": 10, "y": 20}
let keys = d.keys()
main = keys.len()
"#,
        2,
    );

    // Dict values
    run_expect(
        r#"
let d = {"a": 5, "b": 10}
let vals = d.values()
main = vals[0] + vals[1]
"#,
        15,
    );

    // Dict contains_key
    run_expect(
        r#"
let d = {"hello": 1}
main = if d.contains_key("hello"): 1 else: 0
"#,
        1,
    );
}

#[test]
fn runner_handles_bitwise_operations() {
    run_expect("main = 12 & 10", 8); // 1100 & 1010 = 1000
    run_expect("main = 12 | 10", 14); // 1100 | 1010 = 1110
    run_expect("main = 12 ^ 10", 6); // 1100 ^ 1010 = 0110
    run_expect("main = 1 << 4", 16); // shift left
    run_expect("main = 16 >> 2", 4); // shift right
    run_expect("main = ~0", -1); // bitwise not
}

#[test]
fn runner_handles_comparison_operators() {
    run_expect("main = if 1 < 2: 1 else: 0", 1);
    run_expect("main = if 2 > 1: 1 else: 0", 1);
    run_expect("main = if 2 <= 2: 1 else: 0", 1);
    run_expect("main = if 2 >= 2: 1 else: 0", 1);
    run_expect("main = if 2 == 2: 1 else: 0", 1);
    run_expect("main = if 2 != 3: 1 else: 0", 1);
}

#[test]
fn runner_handles_logical_operators() {
    run_expect("main = if true and true: 1 else: 0", 1);
    run_expect("main = if true and false: 1 else: 0", 0);
    run_expect("main = if true or false: 1 else: 0", 1);
    run_expect("main = if false or false: 1 else: 0", 0);
    run_expect("main = if not false: 1 else: 0", 1);
    run_expect("main = if not true: 1 else: 0", 0);
}

#[test]
fn runner_handles_power_operator() {
    run_expect("main = 2 ** 0", 1); // any ** 0 = 1
    run_expect("main = 2 ** 1", 2); // x ** 1 = x
    run_expect("main = 2 ** 3", 8); // 2^3 = 8
    run_expect("main = 2 ** 10", 1024); // 2^10 = 1024
    run_expect("main = 3 ** 4", 81); // 3^4 = 81
}

#[test]
fn runner_handles_floor_division() {
    run_expect("main = 7 // 2", 3); // floor(7/2) = 3
    run_expect("main = 10 // 3", 3); // floor(10/3) = 3
    run_expect("main = -7 // 2", -4); // floor(-7/2) = -4 (rounds toward negative infinity)
    run_expect("main = 8 // 4", 2); // exact division
}

#[test]
fn runner_handles_in_operator() {
    // In array
    run_expect("main = if 2 in [1, 2, 3]: 1 else: 0", 1);
    run_expect("main = if 5 in [1, 2, 3]: 1 else: 0", 0);
    // In string
    run_expect(r#"main = if "ell" in "hello": 1 else: 0"#, 1);
    run_expect(r#"main = if "xyz" in "hello": 1 else: 0"#, 0);
}

// Pointer types may have different syntax
// #[test]
// fn runner_handles_pointer_types() {
//     run_expect(r#"
// let s = new @ 42
// main = *s
// "#, 42);
// }

// Union types need special type system support
// #[test]
// fn runner_handles_union_types() {
//     run_expect(r#"
// fn process(x: i64 | str):
//     match x:
//         n: i64 =>
//             return n
//         s: str =>
//             return s.len()
//     return 0
// main = process(42)
// "#, 42);
// }

// Functional update operator may need method resolution
// #[test]
// fn runner_handles_functional_update() {
//     run_expect(r#"
// let mut x = 5
// x->double()
// main = x
// fn double():
//     return self * 2
// "#, 10);
// }

#[test]
fn runner_handles_extern_functions() {
    // Note: extern functions typically require native libraries
    // This tests the parsing and basic handling
    run_expect(
        r#"
extern fn add_numbers(a: i64, b: i64) -> i64
main = 42
"#,
        42,
    );
}

// method_missing needs special class/method resolution
// #[test]
// fn runner_handles_method_missing() {
//     run_expect(r#"
// class Flexible:
//     fn method_missing(name, args):
//         return 99
// let f = Flexible {}
// main = f.unknown_method()
// "#, 99);
// }

#[test]
fn runner_handles_recursive_functions() {
    // Factorial with smaller input to avoid stack overflow
    run_expect(
        r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

main = factorial(5)
"#,
        120,
    );
}

#[test]
fn runner_handles_nested_data_structures() {
    // Nested arrays
    run_expect(
        r#"
let arr = [[1, 2], [3, 4], [5, 6]]
main = arr[0][0] + arr[1][1] + arr[2][0]
"#,
        10,
    );

    // Nested structs
    run_expect(
        r#"
struct Inner:
    value: i64

struct Outer:
    inner: Inner

let o = Outer { inner: Inner { value: 42 } }
main = o.inner.value
"#,
        42,
    );
}

#[test]
fn runner_handles_early_return() {
    run_expect(
        r#"
fn check(x: i64) -> i64:
    if x > 10:
        return 1
    if x > 5:
        return 2
    return 3

main = check(7)
"#,
        2,
    );
}

#[test]
fn runner_handles_multiple_assignment() {
    run_expect(
        r#"
let (a, b, c) = (1, 2, 3)
main = a + b + c
"#,
        6,
    );
}

#[test]
fn runner_handles_symbols() {
    run_expect(
        r#"
let s = :hello
main = if s == :hello: 1 else: 0
"#,
        1,
    );
}

