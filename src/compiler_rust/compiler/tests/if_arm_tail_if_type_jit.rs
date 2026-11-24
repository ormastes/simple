//! A multiline `if` arm whose tail is itself an `if`/`else` STATEMENT
//! (`val xs = if c:\n    if b: f() else: g()\nelse:\n    []`) must give the
//! arm the inner `if`'s value type. HIR typed that arm NIL, so the join took
//! the empty literal's default `[i32]` and every element read was narrowed
//! to i32: `browser_font_family_for_style` returned
//! `__simple_font_face__|<pointer>|sans-serif` under the JIT and every italic
//! run of the web renderer was painted upright.
//! doc/08_tracking/bug/jit_if_arm_tail_if_stmt_typed_nil_italic_lost_2026-11-23.md

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

const FACES: &str = r#"
fn a_faces() -> [text]:
    ["/a/A.ttf"]

fn b_faces() -> [text]:
    ["/b/B.ttf"]
"#;

#[test]
fn tail_if_arm_joined_with_empty_literal_keeps_text_elements() {
    let src = format!(
        "{FACES}{}",
        r#"
fn pick(cat: text, bold: bool) -> text:
    val faces = if cat == "sans":
        if bold: a_faces() else: b_faces()
    else:
        []
    if faces.len() == 0:
        return "none"
    "face|" + faces[0]

fn main() -> i64:
    var ok = 0
    if pick("sans", false) == "face|/b/B.ttf":
        ok = ok + 1
    if pick("sans", true) == "face|/a/A.ttf":
        ok = ok + 10
    if pick("mono", true) == "none":
        ok = ok + 100
    ok
"#
    );
    assert_eq!(run(&src), 111);
}

#[test]
fn tail_if_arms_in_elif_chain_keep_text_elements() {
    // The exact shape of `browser_font_family_for_style`.
    let src = format!(
        "{FACES}{}",
        r#"
fn pick(cat: text, bold: bool) -> text:
    val faces = if cat == "mono":
        if bold: a_faces() else: b_faces()
    elif cat == "sans":
        if bold: b_faces() else: a_faces()
    else:
        []
    if faces.len() == 0:
        return "none"
    "face|" + faces[0]

fn main() -> i64:
    var ok = 0
    if pick("mono", false) == "face|/b/B.ttf":
        ok = ok + 1
    if pick("sans", false) == "face|/a/A.ttf":
        ok = ok + 10
    if pick("serif", false) == "none":
        ok = ok + 100
    ok
"#
    );
    assert_eq!(run(&src), 111);
}

#[test]
fn tail_if_arm_with_scalar_value_unchanged() {
    let src = r#"
fn pick(c: bool, b: bool) -> i64:
    val n = if c:
        if b: 7 else: 9
    else:
        3
    n

fn main() -> i64:
    pick(true, true) * 100 + pick(true, false) * 10 + pick(false, true)
"#;
    assert_eq!(run(src), 793);
}
