//! Tests for AOT Cranelift compilation

use super::*;
use crate::hir;
use crate::mir::lower_to_mir;
use simple_parser::Parser;

fn compile_to_object(source: &str) -> CodegenResult<Vec<u8>> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    let mir_module = lower_to_mir(&hir_module).expect("mir lower failed");
    Codegen::new()?.compile_module(&mir_module)
}

#[test]
fn test_compile_simple_function() {
    let obj = compile_to_object("fn answer() -> i64:\n    return 42\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_add_function() {
    let obj = compile_to_object("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_comparison() {
    let obj = compile_to_object("fn is_positive(x: i64) -> bool:\n    return x > 0\n").unwrap();
    assert!(!obj.is_empty());
}

#[test]
fn test_compile_if_else() {
    let obj = compile_to_object(
        "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
    ).unwrap();
    assert!(!obj.is_empty());
}
