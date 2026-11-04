//! `[T].first/last/pop/min/max` return a nullable `T?` (element, or nil when
//! empty), matching pure Simple `rt_array_first` -- not `Option<T>`. They must
//! work under `??` and `if val` on the JIT, including present elements whose
//! raw word collides with the nil sentinels (0 and 3), while a plain
//! `val x = xs.first()` binding keeps working.
//! Bug: list_first_returns_raw_value_not_option_2026-07-20

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
fn first_last_coalesce_nonempty_and_empty() {
    let src = "fn main() -> i64:\n    val xs: [i64] = [10, 20, 30]\n    val es: [i64] = []\n    val a = xs.first() ?? 0 - 1\n    val b = xs.last() ?? 0 - 1\n    val c = es.first() ?? 7\n    val d = es.last() ?? 8\n    a * 1000000 + b * 10000 + c * 100 + d\n";
    assert_eq!(run(src), 10 * 1000000 + 30 * 10000 + 7 * 100 + 8);
}

#[test]
fn min_max_coalesce_nonempty_and_empty() {
    let src = "fn main() -> i64:\n    val xs: [i64] = [5, 2, 9]\n    val es: [i64] = []\n    val a = xs.min() ?? 50\n    val b = xs.max() ?? 50\n    val c = es.min() ?? 6\n    val d = es.max() ?? 7\n    a * 1000000 + b * 10000 + c * 100 + d\n";
    assert_eq!(run(src), 2 * 1000000 + 9 * 10000 + 6 * 100 + 7);
}

#[test]
fn pop_coalesce_nonempty_and_empty() {
    let src = "fn main() -> i64:\n    var xs: [i64] = [1, 2, 4]\n    var es: [i64] = []\n    val a = xs.pop() ?? 50\n    val c = es.pop() ?? 6\n    a * 100 + c * 10 + xs.len()\n";
    assert_eq!(run(src), 4 * 100 + 6 * 10 + 2);
}

/// Present 0 and 3 collide with the raw nil words; presence is the tag.
#[test]
fn present_zero_and_three_are_not_nil() {
    let src = "fn main() -> i64:\n    val t: [i64] = [3]\n    val z: [i64] = [0]\n    val a = t.first() ?? 9\n    val b = z.first() ?? 9\n    val c = t.max() ?? 9\n    val d = t.last() ?? 9\n    a * 1000 + b * 100 + c * 10 + d\n";
    assert_eq!(run(src), 3 * 1000 + 0 + 3 * 10 + 3);
}

#[test]
fn if_val_binds_present_and_skips_empty() {
    let src = "fn main() -> i64:\n    val xs: [i64] = [7, 8]\n    val es: [i64] = []\n    var got = 0\n    if val f = xs.first():\n        got = got + f\n    if val l = xs.last():\n        got = got + l * 10\n    if val mn = xs.min():\n        got = got + mn * 100\n    if val mx = xs.max():\n        got = got + mx * 1000\n    var hit = 0\n    if val e1 = es.first():\n        hit = hit + 1\n    if val e2 = es.last():\n        hit = hit + 1\n    if val e3 = es.min():\n        hit = hit + 1\n    if val e4 = es.max():\n        hit = hit + 1\n    got * 10 + hit\n";
    assert_eq!(run(src), (7 + 80 + 700 + 8000) * 10);
}

/// A raw `val x = xs.first()` binding (no absence test) must keep working.
#[test]
fn plain_binding_of_first_still_works() {
    let src = "fn main() -> i64:\n    val xs: [i64] = [41, 2]\n    val f = xs.first()\n    val l = xs.last()\n    f + l\n";
    assert_eq!(run(src), 43);
}
