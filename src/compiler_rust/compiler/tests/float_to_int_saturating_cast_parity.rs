//! Float -> integer conversions agree on every seed engine.
//!
//! The interpreter (the reference engine) converts with Rust `as`
//! (`semantics::cast_float_to_numeric`): truncate toward zero, SATURATE to the
//! target range, NaN -> 0. The Cranelift lowering (JIT `simple run` and
//! native-build share it) used `fcvt_to_{sint,uint}.i64` + `ireduce`, so
//! `70000.5.to_u16()` wrapped to 4464 and `(-5.5).to_u8()` TRAPPED (SIGILL).
//! Covers every integer width, both `to_*()` and `as`, f64 and f32 sources,
//! a call-result receiver and a field receiver, with negative, fractional,
//! out-of-range, +/-inf and NaN inputs.
//! Bug: doc/08_tracking/bug/compiled_float_to_narrow_uint_wraps_or_traps_vs_interpreter_saturates_2026-11-23.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::semantics::{cast_float_to_numeric, CastNumericResult, NumericType};
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

/// (Simple expression producing the f64 input, the same value in Rust)
const INPUTS: &[(&str, f64)] = &[
    ("-5.5", -5.5),
    ("-1.0", -1.0),
    ("-0.5", -0.5),
    ("0.0", 0.0),
    ("3.7", 3.7),
    ("127.9", 127.9),
    ("128.5", 128.5),
    ("-129.5", -129.5),
    ("255.9", 255.9),
    ("256.0", 256.0),
    ("70000.5", 70000.5),
    ("-40000.25", -40000.25),
    ("2147483648.0", 2147483648.0),
    ("-2147483649.0", -2147483649.0),
    ("4294967296.5", 4294967296.5),
    ("10000000000000000000.0", 1e19),
    ("100000000000000000000.0", 1e20),
    ("-100000000000000000000.0", -1e20),
    ("0.0 / 0.0", f64::NAN),
    ("1.0 / 0.0", f64::INFINITY),
    ("-1.0 / 0.0", f64::NEG_INFINITY),
];

const TARGETS: &[&str] = &["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"];

/// The interpreter's conversion, as the i64 the test functions return.
fn reference(value: f64, target: &str) -> i64 {
    match cast_float_to_numeric(value, NumericType::from_name(target).unwrap()) {
        CastNumericResult::Int(v) => v,
        CastNumericResult::Float(_) => unreachable!("integer target"),
    }
}

fn i64_literal(v: i64) -> String {
    if v == i64::MIN {
        "(-9223372036854775807 - 1)".to_string()
    } else {
        v.to_string()
    }
}

/// One zero-argument `-> i64` function per row, plus `main` returning the
/// 1-based index of the first row whose value differs from the reference.
fn build_source() -> (String, Vec<(String, i64)>) {
    let mut src = String::from(
        "class Holder:\n    v: f64\n\nfn ident(x: f64) -> f64:\n    x\n\n",
    );
    let mut rows: Vec<(String, i64)> = Vec::new();
    for (ii, (expr, value)) in INPUTS.iter().enumerate() {
        let f32_value = *value as f32 as f64;
        for t in TARGETS {
            let mut add = |shape: &str, body: String, want: i64| {
                let name = format!("c{ii}_{shape}_{t}");
                src.push_str(&format!("fn {name}() -> i64:\n{body}\n"));
                rows.push((name, want));
            };
            let want = reference(*value, t);
            add("to", format!("    val x: f64 = {expr}\n    x.to_{t}() as i64\n"), want);
            add("as", format!("    val x: f64 = {expr}\n    (x as {t}) as i64\n"), want);
            add("call", format!("    ident({expr}).to_{t}() as i64\n"), want);
            add(
                "field",
                format!("    val h = Holder(v: {expr})\n    h.v.to_{t}() as i64\n"),
                want,
            );
            add(
                "f32",
                format!("    val x: f64 = {expr}\n    val y: f32 = x.to_f32()\n    y.to_{t}() as i64\n"),
                reference(f32_value, t),
            );
        }
        let mut add_int = |shape: &str, body: String| {
            let name = format!("c{ii}_{shape}");
            src.push_str(&format!("fn {name}() -> i64:\n{body}\n"));
            rows.push((name, reference(*value, "i64")));
        };
        add_int("to_int", format!("    val x: f64 = {expr}\n    x.to_int()\n"));
    }
    src.push_str("fn main() -> i64:\n");
    for (i, (name, want)) in rows.iter().enumerate() {
        src.push_str(&format!("    if {name}() != {}: return {}\n", i64_literal(*want), i + 1));
    }
    src.push_str("    return 0\n");
    (src, rows)
}

#[test]
fn compiled_float_to_int_matches_interpreter_saturation() {
    let (source, rows) = build_source();
    let ast = Parser::new(&source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let mut failures = Vec::new();
    for (name, want) in &rows {
        let got = unsafe { jit.call_i64_void(name).expect("function must execute") };
        if got != *want {
            failures.push(format!("{name}: JIT {got}, interpreter {want}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} float->int rows differ from the interpreter:\n{}",
        failures.len(),
        rows.len(),
        failures.join("\n")
    );
}

#[test]
fn interpreter_float_to_int_rows_match_reference() {
    let (source, rows) = build_source();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{source}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    let first_bad = interpreter::evaluate_module(&module.items).expect("source must run in interpreter");
    assert_eq!(
        first_bad,
        0,
        "interpreter differs from the reference at row {}",
        rows.get((first_bad as usize).wrapping_sub(1)).map(|r| r.0.as_str()).unwrap_or("?")
    );
}
