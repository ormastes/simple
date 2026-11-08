//! Regression: jit_class_equality_false_and_invalid_heap_print_2026-11-06.
//!
//! Under the Cranelift JIT, `==` on two field-equal class objects returned
//! false and rendering one produced `<invalid-heap:0x..>`, while the
//! tree-walk interpreter answered `true` / `P(x: 1)`. Both engines must agree.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn equal_class_objects_compare_equal() {
    let source = r#"
class P:
    x: i64

fn main() -> i64:
    val a = P(x: 1)
    val b = P(x: 1)
    if not (a == b): return 1
    if a != b: return 2
    return 42
"#;
    assert_eq!(run(source), 42, "field-equal class objects must compare equal under JIT");
}

#[test]
fn unequal_class_objects_compare_unequal() {
    let source = r#"
class P:
    x: i64
    y: text

fn main() -> i64:
    val a = P(x: 1, y: "a")
    val b = P(x: 2, y: "a")
    val c = P(x: 1, y: "b")
    if a == b: return 1
    if a == c: return 2
    if not (a != b): return 3
    if not (a == a): return 4
    return 42
"#;
    assert_eq!(run(source), 42);
}

#[test]
fn class_object_renders_fields_not_invalid_heap() {
    let source = r#"
class P:
    x: i64

fn main() -> i64:
    val a = P(x: 1)
    val s = "{a}"
    if s.contains("invalid-heap"): return 1
    if s != "P(x: 1)": return 2
    return 42
"#;
    assert_eq!(run(source), 42, "class object must render as P(x: 1) under JIT");
}

#[test]
fn print_class_object_and_text_field_render_without_crash() {
    let source = r#"
class P:
    x: i64
    y: text

fn main() -> i64:
    val a = P(x: 1, y: "s")
    print(a)
    val s = "{a}"
    if s != "P(x: 1, y: s)": return 1
    return 42
"#;
    assert_eq!(run(source), 42);
}
