//! Cranelift JIT: `spl_f64_to_bits` / `spl_bits_to_f64` are lowered inline
//! (`codegen/instr/calls.rs`, bitcast) and need no runtime symbol, so the
//! driver must not splice their callers through the interpreter bridge.
//! `is_inline_lowered_byte_accessor` (the driver's splice exemption) did not
//! list them, so `run` demoted every caller (`[engine-demotion]
//! reason=hybrid-interp-splice detail=spl_f64_to_bits`). This test also pins the
//! values the 2026-07-23 record found corrupt on the compiled path: the bits,
//! an `[i64]` store/readback, and i64 equality.
//! doc/08_tracking/bug/seed_jit_spl_f64_to_bits_miscompile_2026-07-23.md

use simple_compiler::codegen::instr::calls::is_inline_lowered_byte_accessor;
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
fn float_bit_intrinsics_are_exempt_from_interpreter_splice() {
    assert!(is_inline_lowered_byte_accessor("spl_f64_to_bits"));
    assert!(is_inline_lowered_byte_accessor("spl_bits_to_f64"));
}

#[test]
fn f64_to_bits_compiled_value_survives_array_and_equality() {
    let source = r#"
extern fn spl_f64_to_bits(value: f64) -> i64
extern fn spl_bits_to_f64(bits: i64) -> f64

fn f64_to_bits(v: f64) -> i64:
    return spl_f64_to_bits(v)

fn main() -> i64:
    val b = f64_to_bits(3.0)
    if b != 4613937818241073152:
        return 1
    var arr: [i64] = [0, 0, 0]
    arr[1] = b
    val readback = arr[1]
    if readback != 4613937818241073152:
        return 2
    if not (readback == b):
        return 3
    if spl_bits_to_f64(b) != 3.0:
        return 4
    0
"#;
    assert_eq!(run(source), 0);
}
