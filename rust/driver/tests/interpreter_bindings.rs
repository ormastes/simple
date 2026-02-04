#![allow(unused_imports)]

//! Interpreter tests - bindings

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_using_struct() {
    let interpreter = Interpreter::new();
    let result = interpreter.run_simple("main = 100").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_const_declaration() {
    let code = r#"
const MAX = 100
main = MAX
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_static_declaration() {
    let code = r#"
static counter = 42
main = counter
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_const_in_expression() {
    let code = r#"
const BASE = 10
const MULTIPLIER = 5
main = BASE * MULTIPLIER
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

// ============= Option Type Tests =============

#[test]
fn interpreter_global_len_function() {
    let code = r#"
arr = [1, 2, 3, 4, 5]
main = len(arr)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

// ============= Line Continuation Tests =============

#[test]
fn interpreter_let_mut_allows_reassignment() {
    let code = r#"
let mut x = 10
x = 42
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_let_immutable_prevents_reassignment() {
    let code = r#"
let x = 10
x = 42
main = x
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("cannot assign"));
}

#[test]
fn interpreter_mut_let_syntax() {
    // Alternative syntax: mut let x = ...
    let code = r#"
mut let y = 5
y = 10
main = y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_let_mut_tuple_destructure() {
    let code = r#"
let mut (a, b) = (1, 2)
a = 10
b = 20
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_let_immutable_tuple_prevents_reassignment() {
    let code = r#"
let (a, b) = (1, 2)
a = 10
main = a
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

// Named arguments are already tested elsewhere in this file

// ============= Trailing Blocks =============

#[test]
fn interpreter_multiple_immutable_borrows() {
    // Multiple immutable borrows allowed
    let code = r#"
let x = 25
let a = &x
let b = &x
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}
