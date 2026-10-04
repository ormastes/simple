//! JIT/interpreter parity for the text -> integer conversions every engine
//! agrees on. The open single-character divergence is documented in
//! doc/08_tracking/bug/to_int_contract_split_char_codepoint_vs_text_parse_2026-10-05.md
//! and deliberately not pinned here. Expected values are the interpreter's.

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

/// `parse_int` is the Option-returning parse: `?? fallback` fires on failure.
#[test]
fn parse_int_none_takes_the_fallback() {
    let src = "fn main() -> i64:\n    val x = \"x\"\n    val e = \"\"\n    val n = \"12\"\n    (x.parse_int() ?? 7) * 10000 + (e.parse_int() ?? 8) * 100 + (n.parse_int() ?? 9)\n";
    assert_eq!(run(src), 7 * 10000 + 8 * 100 + 12);
}

/// `to_int` is total: numeric text parses, multi-character non-numeric text is 0.
#[test]
fn to_int_is_total_on_agreed_inputs() {
    let src = "fn main() -> i64:\n    val a = \"12\"\n    val b = \" 7 \"\n    val c = \"-5\"\n    val d = \"xy\"\n    val e = \"\"\n    val f = \"12x\"\n    a.to_int() * 1000000 + b.to_int() * 10000 + (c.to_int() + 5) * 100 + d.to_int() + e.to_int() + f.to_int()\n";
    assert_eq!(run(src), 12 * 1_000_000 + 7 * 10_000);
}
