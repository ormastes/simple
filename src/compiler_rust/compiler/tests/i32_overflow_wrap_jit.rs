//! Cranelift JIT: signed `i32` arithmetic wraps at 32 bits on BOTH edges.
//!
//! `compile_binop` computes every integer op in i64. The `i32::MAX + 1` edge
//! only appeared to wrap because the result was stored into an `i32` local
//! (the store narrowed it); `(k - 1)` used directly as an operand never passed
//! through a narrowing store, so `i32::MIN - 1` came out as `-2147483649`.
//! The interpreter wraps both edges (declared-width arithmetic), so the JIT
//! was the inconsistent engine.
//! doc/08_tracking/bug/seed_i32_overflow_interp_vs_jit_divergence_2026-11-05.md
//!
//! `main` returns 0 on success and a distinct case number otherwise.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn i32_arithmetic_wraps_on_both_edges_without_a_narrowing_store() {
    let source = r#"
fn dec(x: i32) -> i64:
    val r = x - 1
    return r

fn main() -> i64:
    val m: i32 = 2147483647
    val n = m + 1
    if n != -2147483648:
        return 1
    val k: i32 = -2147483648
    if (k - 1) != 2147483647:
        return 2
    if (m + 1) != -2147483648:
        return 3
    if dec(k) != 2147483647:
        return 4
    val big: i32 = 65536
    if (big * big) != 0:
        return 5
    val ok: i32 = 100
    if (ok - 1) != 99:
        return 6
    if (k + 0) != -2147483648:
        return 7
    if (1 - k) != -2147483647:
        return 8
    0
"#;
    assert_eq!(run(source), 0);
}

#[test]
fn narrow_unsigned_and_i16_arithmetic_wraps() {
    let source = r#"
fn main() -> i64:
    val u: u32 = 0
    if (u - 1) != 4294967295:
        return 1
    val s: i16 = -32768
    if (s - 1) != 32767:
        return 2
    val b: u8 = 255
    if (b + 1) != 0:
        return 3
    0
"#;
    assert_eq!(run(source), 0);
}
