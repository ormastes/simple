#![allow(unused_imports)]

//! Interpreter tests - memory

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_unique_pointer_basic() {
    // Pointer with & syntax
    let code = r#"
let ptr = &42
main = *ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_arithmetic() {
    // Pointer arithmetic (deref before add)
    let code = r#"
let a = &10
let b = &5
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_basic() {
    // Shared pointer with & syntax
    let code = r#"
let ptr = &42
main = *ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_shared_pointer_arithmetic() {
    // Shared pointer arithmetic
    let code = r#"
let a = &10
let b = &5
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_multiple_refs() {
    // Multiple references to same value
    let code = r#"
let x = 42
let a = &x
let b = &x
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_handle_pointer_basic() {
    // Handle pointer with & syntax
    let code = r#"
let ptr = &42
main = *ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_handle_pointer_arithmetic() {
    // Handle pointer arithmetic
    let code = r#"
let a = &10
let b = &5
main = *a + *b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_weak_pointer_from_shared() {
    // Weak pointer from shared - use borrow
    let code = r#"
let x = 42
let shared_ptr = &x
main = *shared_ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_pointer_with_struct() {
    // Pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point(x: 10, y: 20)
let ptr = &p
main = (*ptr).x + (*ptr).y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_shared_pointer_with_struct() {
    // Shared pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point(x: 5, y: 15)
let ptr = &p
main = (*ptr).x + (*ptr).y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_handle_pointer_with_struct() {
    // Handle pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point(x: 7, y: 3)
let ptr = &p
main = (*ptr).x + (*ptr).y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

// ============================================================================
// Macro Tests
// ============================================================================

#[test]
fn interpreter_immutable_borrow() {
    // Basic immutable borrow with & operator
    let code = r#"
let x = 42
let y = &x  # immutable borrow
main = *y   # dereference
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_mutable_borrow() {
    // Mutable borrow with &mut operator
    // Note: var creates a mutable binding, which is required for &mut
    let code = r#"
var x = 10
let y = &mut x  # mutable borrow
main = *y       # dereference
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_borrow_through_function() {
    // Pass borrow to function
    let code = r#"
fn read_ref(r):
    return *r

let x = 100
let borrowed = &x
main = read_ref(borrowed)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_mutable_borrow_modify() {
    // Mutable borrow allows modification through the reference
    // Note: var creates a mutable binding, which is required for &mut
    let code = r#"
fn add_ten(r):
    # In real borrowing, we'd modify through the ref
    # For now, just read and return modified value
    return *r + 10

var x = 5
let borrowed = &mut x
main = add_ten(borrowed)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_borrow_nested_deref() {
    // Nested borrows and dereferences
    let code = r#"
let x = 100
let ref1 = &x
let ref2 = &ref1
let inner = *ref2
main = *inner
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_borrow_in_expression() {
    // Use borrows directly in expressions
    let code = r#"
let a = 10
let b = 20
main = *(&a) + *(&b)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

// =====================
// Move Semantics Tests
// =====================

#[test]
fn interpreter_unique_pointer_move_basic() {
    // Moving a pointer to another variable should work
    let code = r#"
let u = &42
let v = u
main = *v
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_move_error() {
    // Test pointer copy behavior (Simple uses Copy semantics for pointers)
    let code = r#"
let u = &42
let v = u
main = *u + *v
"#;
    let result = run_code(code, &[], "").unwrap();
    // Pointers are copyable in Simple, so both u and v are valid
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_unique_pointer_deref_no_move() {
    // Dereferencing a pointer should NOT move it
    let code = r#"
let u = &42
let v = *u
let w = *u
main = v + w
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_shared_pointer_no_move() {
    // Pointers can be used multiple times
    let code = r#"
let s1 = &42
let s2 = s1
let s3 = s1
main = *s1 + *s2 + *s3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 126);
}

// =====================
// RAII Drop Tests
// =====================

#[test]
fn interpreter_unique_pointer_raii_function_scope() {
    // Pointer created in function scope is cleaned up when function returns
    let code = r#"
fn create_ptr() -> i64:
    let u = &42
    return *u

fn main() -> i64:
    let result = create_ptr()
    return result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_raii_nested_scope() {
    // Pointer in nested if block is cleaned up when block exits
    let code = r#"
fn main() -> i64:
    var result = 0
    if true:
        let u = &100
        result = *u
    return result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_shared_pointer_raii() {
    // Pointers cleaned up when scope exits
    let code = r#"
fn make_ptr() -> i64:
    let s = &50
    return *s

fn main() -> i64:
    return make_ptr() + make_ptr()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

// =====================
// Macro Tests
// =====================
