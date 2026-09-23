//! Executable regression for raw `char` values crossing into tagged text.
//!
//! A `char` is an untagged Unicode scalar. Passing it to
//! `rt_value_to_string` interprets the scalar's low bits as a RuntimeValue
//! tag and used to produce placeholders such as `<special:15>`. This test
//! executes the generated call path, so checking the MIR call name alone
//! cannot make it pass.

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
fn char_to_text_executes_the_unicode_bridge() {
    let source = r#"
fn main() -> i64:
    if (123 as char).to_text() != "{": return 1
    if (125 as char).to_text() != "}": return 2
    if (233 as char).to_text() != "é": return 3
    if (26085 as char).to_text() != "日": return 4
    if (128578 as char).to_text() != "🙂": return 5
    return 42
"#;

    assert_eq!(
        run(source),
        42,
        "char.to_text() must produce the Unicode character instead of a RuntimeValue placeholder"
    );
}
