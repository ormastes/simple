//! JIT-executed parity checks for values that cross the tagged/raw boundary.
//! Each `main` returns 0 when the JIT agrees with the interpreter's answer and
//! a distinct non-zero code naming the first divergence otherwise.
//! See doc/08_tracking/bug/jit_any_condition_tagged_false_truthy_tls_fetch_2026-10-05.md.

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

/// `for b in bytes` over a byte-packed `[u8]`: the inline array read returned
/// the RAW byte, so a byte that is a multiple of 8 was shifted on decode
/// (104 read as 13; 101 passed through).
#[test]
fn for_in_over_packed_bytes_reads_every_byte() {
    let source = r#"
fn main() -> i64:
    var bytes: [u8] = []
    bytes.push(104u8)
    bytes.push(101u8)
    bytes.push(8u8)
    bytes.push(0u8)
    bytes.push(248u8)
    var sum = 0
    var first = -1
    for b in bytes:
        if first < 0:
            first = b as i64
        sum = sum + (b as i64)
    if first != 104: return 1
    if sum != 461: return 2
    0
"#;
    assert_eq!(run(source), 0);
}

/// `text * int` is repetition; it used to be a native multiply on the string
/// pointer (`"x" * 4000` had len -1).
#[test]
fn text_times_int_repeats() {
    let source = r#"
fn main() -> i64:
    val a = "x" * 4000
    if a.len() != 4000: return 1
    val n = 3
    val b = "ab" * n
    if b != "ababab": return 2
    val c: text = 2 * "yz"
    if c != "yzyz": return 3
    val z = "q" * 0
    if z.len() != 0: return 4
    0
"#;
    assert_eq!(run(source), 0);
}
