//! Floats carried across MIR blocks reach float->int casts as i64-coerced
//! Variables (promoted-f64 bits). The float->int `Cast` arm used to convert
//! those bits as an integer. These shapes must agree with the interpreter.
//! doc/08_tracking/bug/jit_cross_block_float_cast_reads_f64_bits_as_int_2026-10-05.md

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

/// An inlined float-returning helper hands its result to the caller through
/// a cross-block `Copy` into the call's dest vreg.
#[test]
fn inlined_float_return_casts_to_int() {
    let src = r#"
fn half(x: f32) -> f32:
    x * 0.5

fn halve_i(v: f32) -> i32:
    half(v) as i32

fn main() -> i64:
    val a = halve_i(-7.0)
    val b = halve_i(9.0)
    (a.to_i64() + 10) * 100 + b.to_i64()
"#;
    // `main` returns the i32 exit-code slot: keep results non-negative.
    assert_eq!(run(src), (-3 + 10) * 100 + 4);
}

#[test]
fn inlined_f64_return_with_branch_casts_to_int() {
    let src = r#"
fn clamp_pos(x: f64) -> f64:
    if x < 0.0:
        return 0.0 - x
    x + 0.25

fn main() -> i64:
    val a = clamp_pos(-2.75) as i64
    val b = clamp_pos(3.5) as i64
    a * 10 + b
"#;
    assert_eq!(run(src), 2 * 10 + 3);
}

#[test]
fn if_expression_float_merge_casts_to_int() {
    let src = r#"
fn pick(c: bool, a: f32, b: f32) -> i32:
    val v = if c: a * 2.0 else: b - 0.25
    v as i32

fn main() -> i64:
    val x = pick(true, -3.6, 0.0)
    val y = pick(false, 0.0, 9.9)
    (x.to_i64() + 10) * 100 + y.to_i64()
"#;
    assert_eq!(run(src), (-7 + 10) * 100 + 9);
}

#[test]
fn loop_carried_f64_accumulator_casts_to_int() {
    let src = r#"
fn sum_to(n: i64) -> i64:
    var acc: f64 = -0.5
    var i: i64 = 0
    while i < n:
        acc = acc + 1.25
        i = i + 1
    acc as i64

fn main() -> i64:
    sum_to(4) * 10 + sum_to(0)
"#;
    assert_eq!(run(src), 4 * 10 + 0);
}

#[test]
fn match_arm_float_value_casts_to_int() {
    let src = r#"
fn scale(k: i64, v: f64) -> i64:
    val r = match k:
        0: v * 0.5
        1: v + 10.75
        _: 0.0 - v
    r as i64

fn main() -> i64:
    scale(0, 9.0) * 10000 + scale(1, 1.5) * 100 + scale(2, 3.9) + 10
"#;
    assert_eq!(run(src), 4 * 10000 + 12 * 100 - 3 + 10);
}
