//! An inlined callee's float parameter forwarded as the caller's vreg crossed
//! into the inlined blocks as an i64-coerced Variable (f64 bits). A later
//! float->int `Cast` read those bits as an integer: `floor_i(-0.41)` gave
//! -1610612736 under the JIT, and Engine2D bitmap `draw_text_bg` glyphs lost
//! most of their coverage.
//! doc/08_tracking/bug/jit_inlined_float_param_cast_reads_f64_bits_as_int_2026-10-05.md

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
fn inlined_f32_to_int_helper_floors_negative_fraction() {
    let src = r#"
fn to_i(v: f32) -> i32:
    v as i32

fn floor_i(v: f32) -> i32:
    val t = to_i(v)
    if (t as f32) > v:
        return t - 1
    t

fn main() -> i64:
    val inv: f32 = 1.0 / 6.0
    val a = 0.5 * inv - 0.5
    floor_i(a).to_i64() * 100 + floor_i(0.75).to_i64() * 10 + floor_i(-2.5).to_i64()
"#;
    assert_eq!(run(src), -100 + 0 - 3);
}

/// Generalization: f64 params, several float params, and an int param next
/// to a float one, all through an inlined helper used across blocks.
#[test]
fn inlined_float_params_keep_value_across_blocks() {
    let src = r#"
fn trunc64(v: f64) -> i64:
    v as i64

fn mix(scale: f32, offset: f64, n: i64) -> i64:
    val a = trunc64(offset)
    if scale > 0.0:
        return a * 1000 + (scale * 10.0) as i64 + n
    a - n

fn main() -> i64:
    mix(1.5, -7.9, 3) + mix(-1.0, 2.2, 1)
"#;
    assert_eq!(run(src), (-7 * 1000 + 15 + 3) + (2 - 1));
}
