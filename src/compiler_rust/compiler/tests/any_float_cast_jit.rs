//! An `any` holding a heap-boxed float, cast to an integer width, must
//! truncate like the interpreter (`41.75 as i64 == 41`). MIR lowering used to
//! decode the source with `UnboxInt` (`rt_value_unbox_int`), which returns a
//! heap value verbatim, so the cast yielded the float box's tagged pointer
//! word (41.75 -> 4244870612817).
//! doc/08_tracking/bug/jit_any_float_cast_to_int_reads_heap_word_2026-11-13.md

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

// `main` returns the i32 exit-code slot: every test keeps its result small
// and non-negative.

#[test]
fn any_float_as_i64_truncates() {
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val f = box_any(41.75)
    unsafe:
        val n = f as i64
        n
"#;
    assert_eq!(run(src), 41);
}

#[test]
fn any_negative_float_as_i32_truncates_toward_zero() {
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val f = box_any(-7.5)
    unsafe:
        val n = f as i32
        n.to_i64() + 100
"#;
    assert_eq!(run(src), 93);
}

#[test]
fn unsafe_optional_any_float_as_i64_truncates() {
    let src = r#"
fn opt_any(flag: bool) -> any?:
    if flag:
        return 41.75
    nil

fn main() -> i64:
    val o = opt_any(true)
    unsafe:
        val n = o as i64
        n
"#;
    assert_eq!(run(src), 41);
}

#[test]
fn generic_and_container_float_elements_as_i64_truncate() {
    let src = r#"
fn id<T>(v: T) -> T:
    v

fn main() -> i64:
    val g: any = id(12.9)
    val xs: [any] = [3.5, 7]
    unsafe:
        val a = g as i64
        val b = xs[0] as i64
        val c = xs[1] as i64
        a * 100 + b * 10 + c
"#;
    assert_eq!(run(src), 12 * 100 + 3 * 10 + 7);
}

#[test]
fn coalesced_optional_any_float_as_i64_truncates() {
    let src = r#"
fn opt_any(flag: bool) -> any?:
    if flag:
        return 41.75
    nil

fn main() -> i64:
    val o = opt_any(true)
    val z = opt_any(false)
    val a = (o ?? 0) as i64
    val b = (z ?? 0) as i64
    a * 10 + b
"#;
    assert_eq!(run(src), 410);
}

#[test]
fn any_int_and_bool_legs_unchanged() {
    // The non-float legs must decode exactly as before: tagged ints (incl.
    // negative), true/false (1/0, not the special word >> 3), and a wide int.
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val i = box_any(42)
    val two = box_any(2)
    val ten = box_any(10)
    val neg = box_any(-6)
    val t = box_any(true)
    val f = box_any(false)
    val w = box_any(9223372036854775807)
    unsafe:
        val a = i as i64
        val b = i as i32
        val c = t as i64
        val d = f as i64
        val e = two as i64
        val g = ten as i64
        val h = neg as i64
        val k = w as i64
        var ok = 0
        if a == 42 and b == 42 and c == 1 and d == 0:
            ok = ok + 1
        if e == 2 and g == 10 and h == -6:
            ok = ok + 10
        if k == 9223372036854775807:
            ok = ok + 100
        ok
"#;
    assert_eq!(run(src), 111);
}
