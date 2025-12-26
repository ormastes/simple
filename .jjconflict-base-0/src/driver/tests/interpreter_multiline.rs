//! Interpreter tests - multi-line syntax patterns
//! Testing patterns from runner_spec.spl to identify parsing issues

use simple_driver::interpreter::run_code;

/// Test 11: Continuation line with more indent (matcher_spec pattern)
/// result = match_exception("ValueError", "some message",
///                          Expected.Exception("ValueError", Option.None))
#[test]
fn continuation_line_call() {
    let code = r#"
fn match_exception(a, b, c):
    return 42

main = match_exception("ValueError", "some message",
                       "expected")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test 11b: Continuation line at same indent level
#[test]
fn continuation_line_same_indent() {
    let code = r#"
fn match_exception(a, b, c):
    return 42

main = match_exception("ValueError", "some message",
"expected")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test 11c: Continuation inside function body
#[test]
fn continuation_line_in_function() {
    let code = r#"
fn match_exception(a, b, c):
    return 42

fn test():
    return match_exception("ValueError", "some message",
                           "expected")

main = test()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test 12: Tuple destructuring assignment (parser_spec pattern)
/// (content, line) = docstrings[0]
#[test]
fn tuple_destructuring_assignment() {
    let code = r#"
let arr = [(10, 20)]
(a, b) = arr[0]
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

/// Test 13: Tuple element access with .0 syntax
/// docstrings[0].0
#[test]
fn tuple_element_access() {
    let code = r#"
let arr = [(10, 20)]
main = arr[0].0 + arr[0].1
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

/// Test 14: Combined patterns from parser_spec
#[test]
fn parser_spec_combined_patterns() {
    let code = r#"
let docstrings = [("content", 1), ("other", 2)]
(content, line) = docstrings[0]
main = line
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

/// Test 1: Basic multi-line function call (no named args)
#[test]
fn multiline_function_call_basic() {
    let code = r#"
fn add(a, b):
    return a + b

main = add(
    1,
    2
)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

/// Test 2: Multi-line function call with named arguments
#[test]
fn multiline_function_call_named_args() {
    let code = r#"
fn greet(name, msg):
    return 42

main = greet(
    name: "test",
    msg: "hello"
)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test 3: Single line struct init with named args (baseline)
#[test]
fn struct_init_single_line() {
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

/// Test 4: Multi-line array literal
#[test]
fn multiline_array_literal() {
    let code = r#"
let arr = [
    1,
    2,
    3
]
main = arr[0] + arr[1] + arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

/// Test 5: Nested function calls (single line baseline)
#[test]
fn nested_function_call_single_line() {
    let code = r#"
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

main = outer(inner(5), inner(3))
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 16); // 10 + 6
}

/// Test 6: Multi-line with nested call in argument
#[test]
fn multiline_with_nested_call() {
    let code = r#"
fn inner(x):
    return x * 2

fn outer(a, b):
    return a + b

main = outer(
    inner(5),
    inner(3)
)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 16);
}

/// Test 7: Multi-line function call with named arg containing nested call
#[test]
fn multiline_named_arg_with_nested_call() {
    let code = r#"
fn make_val(x):
    return x

fn process(val, extra):
    return val + extra

main = process(
    val: make_val(10),
    extra: 5
)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

/// Test 8: Array with multi-line function calls inside
#[test]
fn array_with_multiline_elements() {
    let code = r#"
fn make(x):
    return x

let arr = [
    make(1),
    make(2)
]
main = arr[0] + arr[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

/// Test 9: Constructor-style call (simulating DoctestExample pattern)
#[test]
fn constructor_style_multiline() {
    let code = r#"
struct Config:
    name: str
    value: i64

fn Config_new(name, value):
    return Config { name: name, value: value }

let c = Config_new(
    "test",
    42
)
main = c.value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test 10: Named args with colon syntax (simulating runner_spec pattern)
#[test]
fn named_args_colon_multiline() {
    let code = r#"
fn build(source, line):
    return line

main = build(
    source: "test",
    line: 42
)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}
