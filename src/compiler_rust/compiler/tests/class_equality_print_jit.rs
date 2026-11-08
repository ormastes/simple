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

/// Text fields built at RUNTIME from distinct allocations (not interned
/// literals) must compare by content, never by pointer.
#[test]
fn runtime_built_text_fields_compare_by_content() {
    let source = r#"
class P:
    x: i64
    y: text

fn main() -> i64:
    val p = "a"
    val q = "b"
    val a = P(x: 1, y: p + q)
    val b = P(x: 1, y: "ab")
    val c = P(x: 1, y: "a" + "b")
    val d = P(x: 1, y: p + "c")
    if not (a == b): return 1
    if a != b: return 2
    if not (a == c): return 3
    if a == d: return 4
    if not (a != d): return 5
    return 42
"#;
    assert_eq!(run(source), 42, "runtime-built equal text fields must compare equal, differing must not");
}

/// Pins the 8-byte-slot-per-field layout assumption for narrow fields.
#[test]
fn mixed_narrow_field_class_equality_and_print() {
    let source = r#"
class N:
    a: u8
    b: i64
    c: bool

fn main() -> i64:
    val x = N(a: 200, b: 123456789012, c: true)
    val y = N(a: 200, b: 123456789012, c: true)
    val z = N(a: 200, b: 123456789012, c: false)
    val w = N(a: 7, b: 123456789012, c: true)
    if not (x == y): return 1
    if x != y: return 2
    if x == z: return 3
    if x == w: return 4
    if not (x != w): return 5
    val s = "{x}"
    if s != "N(a: 200, b: 123456789012, c: true)": return 6
    return 42
"#;
    assert_eq!(run(source), 42, "narrow fields must keep 8-byte slots under field-wise eq/print");
}
