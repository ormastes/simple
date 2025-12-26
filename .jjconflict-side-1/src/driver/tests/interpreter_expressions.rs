#![allow(unused_imports)]

//! Interpreter tests - expressions

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_arithmetic() {
    let result = run_code("main = 10 + 20 * 2", &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_arithmetic_complex() {
    let result = run_code("main = (5 + 3) * 4 - 10 / 2", &[], "").unwrap();
    assert_eq!(result.exit_code, 27); // (5+3)*4 - 10/2 = 32 - 5 = 27
}

#[test]
fn interpreter_symbols() {
    let code = r#"
let status = :ok
main = if status is :ok: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_symbols_comparison() {
    let code = r#"
let a = :hello
let b = :hello
let c = :world
main = if a is b: 10 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_named_arguments_basic() {
    // Basic named arguments
    let code = r#"
fn greet(name, greeting):
    return 1

main = greet(name="world", greeting="hello")
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_named_arguments_reorder() {
    // Named arguments can be in any order
    let code = r#"
fn sub(a, b):
    return a - b

main = sub(b=10, a=30)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20); // 30 - 10 = 20
}

#[test]
fn interpreter_named_arguments_mixed() {
    // Mix positional and named arguments
    let code = r#"
fn calc(x, y, z):
    return x + y * z

main = calc(2, z=4, y=3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 14); // 2 + 3 * 4 = 14
}

#[test]
fn interpreter_functional_update_array_concat() {
    let code = r#"
arr = [1, 2]
arr->concat([3, 4])
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_functional_update_array_map() {
    let code = r#"
arr = [1, 2, 3]
arr->map(\x: x * 2)
main = arr[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4); // [2, 4, 6][1] = 4
}

#[test]
fn interpreter_functional_update_array_filter() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
arr->filter(\x: x > 2)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // [3, 4, 5]
}

#[test]
fn interpreter_functional_update_dict_set() {
    let code = r#"
d = {"a": 1}
d->set("b", 2)
main = d.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2);
}

#[test]
fn interpreter_functional_update_chained() {
    let code = r#"
arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // [2,3,4] -> [3,4]
}

// ============= No-Parentheses Calls (statement level only) =============
// Note: No-parens calls only work for direct statement-level calls,
// NOT inside expressions like assignments.

#[test]
fn interpreter_no_paren_call_simple_statement() {
    // No-parens call at statement level with an argument
    // Call result is ignored, main is set separately
    let code = r#"
fn process(x):
    return x * 2

# Call without parens at statement level (result ignored)
process 10
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_no_paren_call_with_string_arg() {
    // No-parens call with a string argument
    let code = r#"
fn get_len(s):
    return len(s)

# len is called via no-parens then we use print for side effect
get_len "hello"
main = 5
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_no_paren_call_with_int_arg() {
    // No-parens call with an integer argument
    let code = r#"
fn double(x):
    return x * 2

# This won't affect main since result is ignored
double 21
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============= Mutability Control =============

#[test]
fn interpreter_trailing_block_method_call() {
    // obj.method \x: body is equivalent to obj.method(\x: body)
    let code = r#"
arr = [1, 2, 3]
doubled = arr.map \x: x * 2
main = doubled[1]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4); // [2, 4, 6][1] = 4
}

#[test]
fn interpreter_trailing_block_with_args() {
    // obj.method(arg) \x: body - trailing block after regular args
    let code = r#"
fn apply_twice(f, x):
    return f(f(x))

res = apply_twice(\n: n + 1, 40)
main = res
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_trailing_block_filter() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
filtered = arr.filter \x: x > 3
main = filtered.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 2); // [4, 5]
}

#[test]
fn interpreter_trailing_block_multi_param() {
    let code = r#"
fn combine(a, b, f):
    return f(a, b)

res = combine(20, 22) \x, y: x + y
main = res
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

// ============ Extern Functions (#46) ============
