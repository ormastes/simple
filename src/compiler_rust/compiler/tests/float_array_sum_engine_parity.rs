//! `[f64].sum()` / `[f32].sum()` agree on the interpreter and the JIT.
//!
//! `rt_array_sum` returns a boxed FLOAT when any element is a float, but HIR
//! typed every `sum` as `I64` and MIR unboxed the result as an int, so the
//! compiled `[1.5, 2.25].sum()` printed a heap address. `main` returns the
//! 1-based number of the first row that differs.
//! Bug: doc/08_tracking/bug/compiled_float_array_sum_reads_boxed_float_as_int_2026-11-24.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn f64_sum(xs: [f64]) -> f64:
    xs.sum()

fn main() -> i64:
    val af: [f64] = [1.5, 2.25]
    val neg: [f64] = [-1.5, 0.5]
    val af32: [f32] = [1.5f32, 2.25f32]
    val one: [f64] = [7.25]
    val big: [f64] = [100000000000000000000.0, 1.0]
    val ai: [i64] = [-5, 7, 9]
    val au: [u32] = [0xffffffffu32, 1u32]
    if af.sum() != 3.75: return 1
    if neg.sum() != -1.0: return 2
    if af32.sum() != 3.75: return 3
    if one.sum() != 7.25: return 4
    if big.sum() != 100000000000000000001.0: return 5
    val s: f64 = af.sum()
    if s * 2.0 != 7.5: return 6
    if f64_sum(af) != 3.75: return 7
    if ai.sum() != 11: return 8
    if au.sum() != 4294967296: return 9
    return 0
"#;

fn run_interpreter(source: &str) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{source}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter")
}

fn run_jit(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn float_array_sum_interpreter() {
    let row = run_interpreter(SOURCE);
    assert_eq!(row, 0, "interpreter failed at row {row}");
}

#[test]
fn float_array_sum_jit() {
    let row = run_jit(SOURCE);
    assert_eq!(row, 0, "JIT failed at row {row}");
}
