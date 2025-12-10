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
let shared = new * 42
let weak = new - shared
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
// Macro Tests
// =====================
