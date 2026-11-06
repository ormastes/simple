//! Cranelift JIT: a guard on a wildcard match arm (`case _ if c:`) must be
//! honoured. HIR match lowering treated every bare `_` arm as irrefutable and
//! returned its body directly, dropping the guard and every later arm, so
//! `case _ if false:` still matched. Both the expression-position chain
//! (`hir/lower/expr/control.rs::lower_match_arms`) and the statement chain
//! (`hir/lower/stmt_lowering.rs::lower_match_arms_stmt`) had the shortcut.
//! Expected values are the interpreter's.
//! doc/08_tracking/bug/seed_run_wildcard_arm_guard_ignored_2026-10-10.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    simple_runtime::register_static_runtime_symbols();
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

/// Expression-position match (function tail value).
#[test]
fn guarded_wildcard_arm_in_value_match_falls_through_when_false() {
    let source = r#"
enum E:
    A
    B

fn d1(n: i64, c: bool) -> i64:
    match n:
        case 1:
            1
        case _ if c:
            3
        case _:
            4

fn d3(e: E, c: bool) -> i64:
    match e:
        case E.A:
            1
        case _ if c:
            3
        case _:
            4

fn main() -> i64:
    d1(5, true) * 1000 + d1(5, false) * 100 + d3(E.B, true) * 10 + d3(E.B, false)
"#;
    assert_eq!(run(source), 3434);
}

/// Statement-position match (arms assign, value read afterwards).
#[test]
fn guarded_wildcard_arm_in_statement_match_falls_through_when_false() {
    let source = r#"
fn s(n: i64, c: bool) -> i64:
    var r = 0
    match n:
        case 1:
            r = 1
        case _ if c:
            r = 3
        case _:
            r = 4
    r

fn main() -> i64:
    s(5, true) * 10 + s(5, false)
"#;
    assert_eq!(run(source), 34);
}
