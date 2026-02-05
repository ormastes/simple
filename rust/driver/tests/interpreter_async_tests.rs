#![allow(unused_imports)]

//! Interpreter tests - async tests

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_lambda_simple() {
    // Basic lambda: \x: expr
    let code = r#"
let double = \x: x * 2
main = double(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_multiple_params() {
    // Lambda with multiple parameters: \x, y: expr
    let code = r#"
let add = \x, y: x + y
main = add(15, 27)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_closure() {
    // Lambda capturing a variable from outer scope
    let code = r#"
let multiplier = 10
let multiply = \x: x * multiplier
main = multiply(4)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40);
}

#[test]
fn interpreter_lambda_immediate_call() {
    // Immediately invoked lambda
    let code = r#"
main = (\x: x + 5)(37)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_lambda_nested() {
    // Nested lambda calls
    let code = r#"
let double = \x: x * 2
let add_one = \x: x + 1
main = add_one(double(20))
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 41); // double(20)=40, add_one(40)=41
}

#[test]
fn interpreter_lambda_no_params() {
    // Lambda with no parameters: \: expr
    let code = r#"
let answer = \: 42
main = answer()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_future_basic() {
    // Create a future and await it
    let code = r#"
let f = future(42)
let value = await f
main = value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_future_with_computation() {
    // Future with actual computation
    let code = r#"
fn compute():
    return 10 + 20 + 30

let f = future(compute())
let value = await f
main = value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_future_multiple() {
    // Multiple futures
    let code = r#"
let f1 = future(10)
let f2 = future(20)
let f3 = future(30)
let r1 = await f1
let r2 = await f2
let r3 = await f3
main = r1 + r2 + r3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_await_non_future() {
    // Await on a non-future value now produces a semantic error
    let code = r#"
let x = 42
let value = await x
main = value
"#;
    let result = run_code(code, &[], "");
    // With stricter type checking, await requires a Future or Actor handle
    assert!(result.is_err());
    let err_msg = result.unwrap_err();
    assert!(
        err_msg.contains("await") && err_msg.contains("Future"),
        "Expected error about await requiring Future, got: {}",
        err_msg
    );
}

#[test]
fn interpreter_future_function_call() {
    // future() creates a future from a function call
    let code = r#"
fn slow_add(a, b):
    return a + b

let f = future(slow_add(15, 27))
let value = await f
main = value
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_async_basic() {
    // async fn can do non-blocking computation
    let code = r#"
async fn compute(x):
    return x * 2

main = compute(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_async_allows_print() {
    // async fn CAN use print (async-compatible I/O)
    // Print is async-aware and doesn't block the async runtime
    let code = r#"
extern fn print(msg)

async fn greet():
    print("hello")
    return 42

main = greet()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_async_allows_await() {
    // async fn CAN use await - that's the whole point of async!
    let code = r#"
async fn compute():
    let f = future(42)
    return await f

main = compute()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_async_fn_basic() {
    // async fn can use blocking operations - auto-awaited at top level
    let code = r#"
async fn fetch():
    return 42

main = fetch()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_async_can_call_async() {
    // async fn can call other async functions
    let code = r#"
async fn double(x):
    return x * 2

async fn quadruple(x):
    return double(double(x))

main = quadruple(10)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40);
}

#[test]
#[ignore] // BLOCKED: Generator syntax not implemented (requires generator JIT)
fn interpreter_generator_basic() {
    // Basic generator test - multiple yields using array
    let code = r#"
let gen = generator(\: [yield 1, yield 2, yield 3])

let first = next(gen)
let second = next(gen)
let third = next(gen)

main = first + second + third
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

#[test]
#[ignore] // BLOCKED: Generator syntax not implemented (requires generator JIT)
fn interpreter_generator_single() {
    // Simple single-value generator
    let code = r#"
let gen = generator(\: yield 42)

main = next(gen)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
#[ignore] // BLOCKED: Generator syntax not implemented (requires generator JIT)
fn interpreter_generator_collect() {
    // Collect all generator values into array
    let code = r#"
let gen = generator(\: (yield 10, yield 20, yield 30, 0)[3])

let arr = collect(gen)
main = arr[0] + arr[1] + arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
#[ignore] // BLOCKED: Generator syntax not implemented (requires generator JIT)
fn interpreter_generator_exhausted() {
    // Generator returns nil when exhausted
    let code = r#"
let gen = generator(\: yield 1)

let first = next(gen)
let second = next(gen)  # should be nil

# nil converts to 0 for main
main = first
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

// ===== Borrowing Tests =====
