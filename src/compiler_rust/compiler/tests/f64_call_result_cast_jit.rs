//! A numeric conversion (or any builtin float method) called DIRECTLY on a call expression that
//! returns f64/f32 (`floor(x).to_i32()`) must convert the value.
//!
//! User functions return floats as raw IEEE-754 bits in an i64 register (MIR
//! still types the result vreg f64). The cast lowering decided float-ness from
//! the Cranelift value type alone, so it narrowed the BIT PATTERN:
//! `47.0.to_i64()` came out as 0x4047800000000000 and `.to_i32()` as 0.
//! Binding the result to a local first hid it, and the interpreter was always
//! right. Bug:
//! doc/08_tracking/bug/native_call_result_f64_to_int_conversion_bits_2026-11-23.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

const SOURCE: &str = "\
fn local_floor(x: f64) -> f64:
    val t = x as i64 as f64
    if t > x: t - 1.0 else: t

fn half32(x: f64) -> f32:
    (x / 2.0) as f32

class Probe:
    v: f64
    fn getf() -> f64:
        self.v

fn to_i32_direct() -> i64:
    local_floor(47.26617698462807).to_i32() as i64

fn to_i64_direct() -> i64:
    local_floor(47.26617698462807).to_i64()

fn to_u8_direct() -> i64:
    local_floor(200.9).to_u8() as i64

fn to_u32_direct() -> i64:
    local_floor(240.3).to_u32() as i64

fn negative_direct() -> i64:
    local_floor(-3.5).to_i32() as i64

fn f32_call_to_i32() -> i64:
    half32(91.0).to_i32() as i64

fn f64_call_to_f32_then_int() -> i64:
    local_floor(12.75).to_f32().to_i64()

fn method_call_to_i32() -> i64:
    val p = Probe(v: 7.9)
    p.getf().to_i32() as i64

fn local_arg_to_i32() -> i64:
    val x = 47.26617698462807
    local_floor(x).to_i32() as i64

fn neg(x: f64) -> f64:
    0.0 - x

fn abs_on_call() -> i64:
    (neg(3.5).abs() * 10.0) as i64

fn sqrt_on_call() -> i64:
    (local_floor(16.2).sqrt() * 10.0) as i64

fn floor_on_call() -> i64:
    neg(2.5).floor() as i64

fn max_on_call() -> i64:
    local_floor(3.7).max(5.0) as i64

fn f32_binop_to_i64() -> i64:
    (local_floor(12.75).to_f32() * 2.0).to_i64()

fn bound_local_control() -> i64:
    val f: f64 = local_floor(47.26617698462807)
    f.to_i32() as i64
";

#[test]
fn cast_method_on_f64_call_result_converts_value_not_bits() {
    let ast = Parser::new(SOURCE).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let cases: &[(&str, i64)] = &[
        ("to_i32_direct", 47),
        ("to_i64_direct", 47),
        ("to_u8_direct", 200),
        ("to_u32_direct", 240),
        ("negative_direct", -4),
        ("f32_call_to_i32", 45),
        ("f64_call_to_f32_then_int", 12),
        ("method_call_to_i32", 7),
        ("local_arg_to_i32", 47),
        ("abs_on_call", 35),
        ("sqrt_on_call", 40),
        ("floor_on_call", -3),
        ("max_on_call", 5),
        ("f32_binop_to_i64", 24),
        ("bound_local_control", 47),
    ];
    let mut failures = Vec::new();
    for (name, want) in cases {
        let got = unsafe { jit.call_i64_void(name).expect("function must execute") };
        if got != *want {
            failures.push(format!("{name}: got {got} (0x{got:x}), want {want}"));
        }
    }
    assert!(failures.is_empty(), "f64 call-result casts converted bits:\n{}", failures.join("\n"));
}
