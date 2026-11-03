//! Host-JIT probes for the C1..C6 defects in
//! simpleos_native_build_entry_closure_codegen_defects_2026-07-17.

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
fn c1_module_global_call_initializer_is_emitted() {
    let src = "fn make() -> i64:\n    41\n\nval G: i64 = make()\n\nfn main() -> i64:\n    G + 1\n";
    assert_eq!(run(src), 42);
}

#[test]
fn c1_module_global_array_initializer_keeps_pushes() {
    let src = "var POOL: [i64] = []\n\nfn add(v: i64):\n    POOL.push(v)\n\nfn main() -> i64:\n    add(3)\n    add(4)\n    POOL.len() * 10 + POOL[1]\n";
    assert_eq!(run(src), 24);
}

#[test]
fn c2_if_val_hit_returns_payload() {
    let src = "fn maybe(n: i64) -> i64?:\n    if n > 0:\n        return n\n    nil\n\nfn pick(n: i64) -> i64:\n    if val x = maybe(n):\n        return x\n    -1\n\nfn main() -> i64:\n    pick(7) * 10 + (pick(0) + 1)\n";
    assert_eq!(run(src), 70);
}

#[test]
fn c3_short_circuit_and_with_call_rhs_tests_lhs() {
    let src = "var CALLS: i64 = 0\n\nfn probe() -> bool:\n    CALLS = CALLS + 1\n    true\n\nfn gate(off: bool) -> i64:\n    if not off and probe():\n        return 1\n    0\n\nfn main() -> i64:\n    val a = gate(true)\n    val b = gate(false)\n    a * 100 + b * 10 + CALLS\n";
    assert_eq!(run(src), 11);
}

#[test]
fn c4_anonymous_tuple_positions() {
    let src = "fn t() -> (i64, i64, i64, i64):\n    (1, 2, 3, 4)\n\nfn main() -> i64:\n    val r = t()\n    r.0 * 1000 + r.1 * 100 + r.2 * 10 + r.3\n";
    assert_eq!(run(src), 1234);
}

#[test]
fn c5_enum_equality() {
    let src = "enum Mode:\n    User\n    System\n\nfn m() -> Mode:\n    Mode.System\n\nfn main() -> i64:\n    val x = m()\n    var r: i64 = 0\n    if x == Mode.System:\n        r = r + 1\n    if x == Mode.User:\n        r = r + 10\n    r\n";
    assert_eq!(run(src), 1);
}

#[test]
fn c6_byte_combine() {
    let src = "fn comb(b0: u32, b1: u32) -> u32:\n    b0 | (b1 << 8)\n\nfn main() -> i64:\n    comb(0x70, 0x0f) as i64\n";
    assert_eq!(run(src), 0x0f70);
}
