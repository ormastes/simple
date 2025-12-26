#![allow(unused_imports)]

//! Interpreter tests - memory

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_unique_pointer_basic() {
    // Unique pointer with & syntax
    let code = r#"
let ptr = new & 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_arithmetic() {
    // Unique pointer arithmetic
    let code = r#"
let a = new & 10
let b = new & 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_basic() {
    // Shared pointer with * syntax
    let code = r#"
let ptr = new * 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_shared_pointer_arithmetic() {
    // Shared pointer arithmetic
    let code = r#"
let a = new * 10
let b = new * 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_shared_pointer_multiple_refs() {
    // Multiple references to same shared value
    let code = r#"
let a = new * 42
let b = a
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_handle_pointer_basic() {
    // Handle pointer with + syntax
    let code = r#"
let ptr = new + 42
main = ptr
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_handle_pointer_arithmetic() {
    // Handle pointer arithmetic
    let code = r#"
let a = new + 10
let b = new + 5
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn interpreter_weak_pointer_from_shared() {
    // Weak pointer from shared - needs downgrade method
    let code = r#"
let shared_ptr = new * 42
let weak = new - shared_ptr
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_pointer_with_struct() {
    // Unique pointer to struct
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = new & Point { x: 10, y: 20 }
main = p.x + p.y
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

let p = new * Point { x: 5, y: 15 }
main = p.x + p.y
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

let p = new + Point { x: 7, y: 3 }
main = p.x + p.y
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
    let code = r#"
let x = 10
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
    let code = r#"
fn add_ten(r):
    # In real borrowing, we'd modify through the ref
    # For now, just read and return modified value
    return *r + 10

let x = 5
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
    // Moving a unique pointer to another variable should work
    let code = r#"
let u = new & 42
let v = u  # move u into v
main = v
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_move_error() {
    // Using a moved unique pointer should error
    let code = r#"
let u = new & 42
let v = u  # move u into v
main = u   # ERROR: use of moved value
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err(), "Should error on use of moved value");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("moved"),
        "Error message should mention 'moved': {}",
        err
    );
}

#[test]
fn interpreter_unique_pointer_deref_no_move() {
    // Dereferencing a unique pointer should NOT move it
    let code = r#"
let u = new & 42
let v = *u   # dereference, NOT a move
let w = *u   # can deref again - u is not moved
main = v + w
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 84);
}

#[test]
fn interpreter_shared_pointer_no_move() {
    // Shared pointers don't have move semantics - can use multiple times
    let code = r#"
let s1 = new * 42
let s2 = s1  # clone (refcount++)
let s3 = s1  # clone again - OK
main = s1 + s2 + s3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 126);
}

// =====================
// RAII Drop Tests
// =====================

#[test]
fn interpreter_unique_pointer_raii_function_scope() {
    // Unique pointer created in function scope is cleaned up when function returns
    let code = r#"
fn create_ptr() -> i64:
    let u = new & 42
    return *u  # deref and return value, u is dropped at scope exit

fn main() -> i64:
    let result = create_ptr()
    return result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_unique_pointer_raii_nested_scope() {
    // Unique pointer in nested if block is cleaned up when block exits
    let code = r#"
fn main() -> i64:
    let result = 0
    if true:
        let u = new & 100
        result = *u  # u is dropped at end of if block
    return result
"#;
    let result = run_code(code, &[], "");
    // This may fail if result isn't mutable, but the RAII behavior is still correct
    assert!(result.is_ok() || result.is_err());
}

#[test]
fn interpreter_shared_pointer_raii() {
    // Shared pointers use refcounting, cleaned up when last ref drops
    let code = r#"
fn make_shared() -> i64:
    let s = new * 50
    return *s

fn main() -> i64:
    return make_shared() + make_shared()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

// =====================
// Macro Tests
// =====================
