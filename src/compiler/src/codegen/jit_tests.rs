//! Tests for JIT compilation

use super::*;
use crate::hir;
use crate::mir::lower_to_mir;
use simple_parser::Parser;

fn jit_compile(source: &str) -> JitResult<JitCompiler> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");

    let mut jit = JitCompiler::new()?;
    jit.compile_module(&mir_module)?;
    Ok(jit)
}

#[test]
fn test_jit_simple_return() {
    let jit = jit_compile("fn answer() -> i64:\n    return 42\n").unwrap();
    let result = unsafe { jit.call_i64_void("answer").unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_add() {
    let jit = jit_compile("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("add", 10, 32).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_subtract() {
    let jit = jit_compile("fn sub(a: i64, b: i64) -> i64:\n    return a - b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("sub", 50, 8).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_multiply() {
    let jit = jit_compile("fn mul(a: i64, b: i64) -> i64:\n    return a * b\n").unwrap();
    let result = unsafe { jit.call_i64_i64_i64("mul", 6, 7).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_negate() {
    let jit = jit_compile("fn neg(x: i64) -> i64:\n    return -x\n").unwrap();
    let result = unsafe { jit.call_i64_i64("neg", -42).unwrap() };
    assert_eq!(result, 42);
}

#[test]
fn test_jit_conditional() {
    let jit = jit_compile(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
    ).unwrap();

    let result1 = unsafe { jit.call_i64_i64_i64("max", 42, 10).unwrap() };
    assert_eq!(result1, 42);

    let result2 = unsafe { jit.call_i64_i64_i64("max", 10, 42).unwrap() };
    assert_eq!(result2, 42);
}

#[test]
fn test_jit_recursive_factorial() {
    let jit = jit_compile(
        r#"fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)
"#,
    )
    .unwrap();

    let result = unsafe { jit.call_i64_i64("factorial", 5).unwrap() };
    assert_eq!(result, 120);
}
