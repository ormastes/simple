//! End-to-end WASM compilation and execution tests
//!
//! These tests verify that Simple code can be compiled to WebAssembly
//! and executed using the Wasmer runtime with WASI support.
//!
//! ## Running WASM Tests
//!
//! WASM tests should be run in **release mode** to avoid wasmer 3.1 debug
//! alignment check issues:
//!
//! ```bash
//! # Run all WASM tests in release mode (recommended)
//! cargo test -p simple-driver --features wasm --release --test wasm_tests
//!
//! # Run a specific test
//! cargo test -p simple-driver --features wasm --release test_wasm_function_call
//! ```
//!
//! ## Known Issue
//!
//! In debug mode, wasmer 3.1 triggers false-positive `ptr::copy` alignment
//! checks during module instantiation. The generated WASM is correct and
//! runs fine in release mode. This is a wasmer bug, not a compiler bug.
//! - Upgrade to wasmer 4.x (requires Rust 1.75+) to fix debug mode

#![cfg(feature = "wasm")]
#![cfg(test)]  // Mark all tests in this file

mod test_helpers;
use test_helpers::{run_expect_wasm, run_expect_wasm_output, run_expect_all_including_wasm};

// ============================================================================
// Basic arithmetic and control flow tests
// ============================================================================

#[test]
fn test_wasm_simple_return() {
    run_expect_wasm("fn main() -> i64:\n    return 42\n", 42);
}

#[test]
fn test_wasm_arithmetic() {
    run_expect_wasm("fn main() -> i64:\n    return 10 + 32\n", 42);
}

#[test]
fn test_wasm_multiplication() {
    run_expect_wasm("fn main() -> i64:\n    return 6 * 7\n", 42);
}

#[test]
fn test_wasm_subtraction() {
    run_expect_wasm("fn main() -> i64:\n    return 50 - 8\n", 42);
}

#[test]
fn test_wasm_division() {
    run_expect_wasm("fn main() -> i64:\n    return 84 / 2\n", 42);
}

#[test]
fn test_wasm_modulo() {
    run_expect_wasm("fn main() -> i64:\n    return 142 % 100\n", 42);
}

#[test]
fn test_wasm_if_true() {
    let code = r#"
fn main() -> i64:
    if true:
        return 42
    else:
        return 0
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_if_false() {
    let code = r#"
fn main() -> i64:
    if false:
        return 0
    else:
        return 42
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_comparison() {
    let code = r#"
fn main() -> i64:
    if 10 > 5:
        return 42
    else:
        return 0
"#;
    run_expect_wasm(code, 42);
}

// ============================================================================
// Variable and function tests
// ============================================================================

#[test]
fn test_wasm_local_variable() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 42
    return x
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_variable_arithmetic() {
    let code = r#"
fn main() -> i64:
    let x: i64 = 10
    let y: i64 = 32
    return x + y
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_function_call() {
    let code = r#"
fn add(a: i64, b: i64) -> i64:
    return a + b

fn main() -> i64:
    return add(10, 32)
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_nested_function_calls() {
    let code = r#"
fn double(x: i64) -> i64:
    return x * 2

fn triple(x: i64) -> i64:
    return x * 3

fn main() -> i64:
    return double(7) * triple(2)
"#;
    run_expect_wasm(code, 84);
}

// ============================================================================
// Floating-point tests
// ============================================================================

#[test]
fn test_wasm_float_arithmetic() {
    let code = r#"
fn main() -> i64:
    let x: f64 = 21.0
    let y: f64 = 2.0
    let result: i64 = (x * y) as i64
    return result
"#;
    run_expect_wasm(code, 42);
}

// ============================================================================
// Boolean logic tests
// ============================================================================

#[test]
fn test_wasm_and_logic() {
    let code = r#"
fn main() -> i64:
    if true and true:
        return 42
    else:
        return 0
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_or_logic() {
    let code = r#"
fn main() -> i64:
    if false or true:
        return 42
    else:
        return 0
"#;
    run_expect_wasm(code, 42);
}

#[test]
fn test_wasm_not_logic() {
    let code = r#"
fn main() -> i64:
    if not false:
        return 42
    else:
        return 0
"#;
    run_expect_wasm(code, 42);
}

// ============================================================================
// Parity tests (verify WASM matches interpreter and JIT)
// ============================================================================

#[test]
fn test_parity_arithmetic() {
    let code = "fn main() -> i64:\n    return 6 * 7\n";
    run_expect_all_including_wasm(code, 42);
}

#[test]
fn test_parity_function_call() {
    let code = r#"
fn fibonacci(n: i64) -> i64:
    if n <= 1:
        return n
    else:
        return fibonacci(n - 1) + fibonacci(n - 2)

fn main() -> i64:
    return fibonacci(10)
"#;
    run_expect_all_including_wasm(code, 55);
}

#[test]
fn test_parity_factorial() {
    let code = r#"
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)

fn main() -> i64:
    return factorial(5)
"#;
    run_expect_all_including_wasm(code, 120);
}

// ============================================================================
// I/O tests (WASI stdio)
// ============================================================================

#[test]
#[cfg(all(feature = "wasm", feature = "wasm-wasi"))]
fn test_wasm_stdio_println() {
    // Uses builtin println which calls rt_println_str -> WASI fd_write
    let code = r#"
fn main() -> i64:
    println("Hello, WASM!")
    return 0
"#;
    run_expect_wasm_output(code, "Hello, WASM!\n");
}

#[test]
#[cfg(all(feature = "wasm", feature = "wasm-wasi"))]
fn test_wasm_stdio_print() {
    // Uses builtin print/println which calls rt_print_str/rt_println_str -> WASI fd_write
    let code = r#"
fn main() -> i64:
    print("Hello")
    print(", ")
    println("WASM!")
    return 0
"#;
    run_expect_wasm_output(code, "Hello, WASM!\n");
}
