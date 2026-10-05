//! A block EXPRESSION's tail value must be coerced to the block's type, not
//! to the enclosing function's return type. `val a = s.parse_int() ?? 8`
//! (lowered as a block) inside an `-> i64` function unboxed its ANY result
//! into an ANY local and was unboxed again on use, so the fallback 8 read as 1.

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
fn coalesce_bound_to_val_keeps_fallback_and_payload() {
    let src = "fn pick(e: text) -> i64:\n    val a = e.parse_int() ?? 8\n    a\n\nfn main() -> i64:\n    val none = \"\"\n    val some = \"12\"\n    pick(none) * 100 + pick(some)\n";
    assert_eq!(run(src), 812);
}

#[test]
fn coalesce_bound_to_val_for_optional_returns() {
    let src = "fn maybe(n: i64) -> i64?:\n    if n > 0:\n        return n\n    nil\n\nfn pick(n: i64) -> i64:\n    val a = maybe(n) ?? 8\n    a\n\nfn main() -> i64:\n    pick(0) * 100 + pick(16)\n";
    assert_eq!(run(src), 816);
}

#[test]
fn coalesce_bool_and_float_fallbacks_round_trip() {
    let src = "fn mb(n: i64) -> bool?:\n    if n > 0:\n        return true\n    nil\n\nfn mf(n: i64) -> f64?:\n    if n > 0:\n        return 2.5\n    nil\n\nfn main() -> i64:\n    val b0 = mb(0) ?? false\n    val b1 = mb(1) ?? false\n    val f0 = mf(0) ?? 4.0\n    val f1 = mf(1) ?? 4.0\n    var r: i64 = 0\n    if not b0:\n        r = r + 1\n    if b1:\n        r = r + 10\n    r + ((f0 + f1) * 10.0) as i64 * 100\n";
    assert_eq!(run(src), 11 + 65 * 100);
}

/// The other `T?` representation: a boxed `Some(x)` enum, plus nil.
#[test]
fn coalesce_bool_and_float_over_boxed_some_and_nil() {
    let src = "fn main() -> i64:\n    val ob: bool? = Some(true)\n    val nb: bool? = nil\n    val of: f64? = Some(1.5)\n    val nf: f64? = nil\n    val b1 = ob ?? false\n    val b0 = nb ?? false\n    val f = (of ?? 9.0) + (nf ?? 0.25)\n    var r: i64 = 0\n    if b1:\n        r = r + 10\n    if not b0:\n        r = r + 1\n    r + (f * 100.0) as i64 * 100\n";
    assert_eq!(run(src), 11 + 175 * 100);
}

#[test]
fn lambda_inside_block_uses_its_own_return_type() {
    let src = "fn main() -> i64:\n    val e = \"\"\n    val f = \\x: x * 3\n    val a = e.parse_int() ?? f(5)\n    a + f(1)\n";
    assert_eq!(run(src), 15 + 3);
}
