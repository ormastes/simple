//! `[uN].sum()` agrees on the interpreter and the JIT.
//!
//! `[u8]`/`[u16]`/`[u32]`/`[u64]` elements are `Value::UInt` in the
//! interpreter; its `sum` arm only added `Value::Int`, so
//! `[0xffffffffu32, 0xffffffffu32, 3u32].sum()` returned 0 while the JIT
//! (`rt_array_sum`) returned 8589934593. min/max already ordered UInt
//! elements; they are pinned here too. `main` returns the 1-based number of
//! the first row that differs.
//! Bug: doc/08_tracking/bug/interp_unsigned_array_sum_returns_zero_2026-11-23.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn main() -> i64:
    val a8: [u8] = [255u8, 255u8, 3u8]
    val a16: [u16] = [65535u16, 65535u16, 3u16]
    val a32: [u32] = [0xffffffffu32, 0xffffffffu32, 3u32]
    val a64: [u64] = [5u64, 7u64, 0xffffffffu64]
    val one8: [u8] = [200u8]
    val empty32: [u32] = []
    val ai: [i64] = [-5, 7, 9]
    if a8.sum() != 513: return 1
    if a16.sum() != 131073: return 2
    if a32.sum() != 8589934593: return 3
    if a64.sum() != 4294967307: return 4
    if one8.sum() != 200: return 5
    if empty32.sum() != 0: return 6
    if ai.sum() != 11: return 7
    if a8.min() != 3u8: return 8
    if a8.max() != 255u8: return 9
    if a16.max() != 65535u16: return 10
    if a32.min() != 3u32: return 11
    if a32.max() != 0xffffffffu32: return 12
    if a64.max() != 0xffffffffu64: return 13
    # The sum is an i64 on every engine: a high-bit u64 wraps two's-complement.
    val hi: [u64] = [0x8000000000000000u64, 1u64]
    val wrap: [u64] = [0xffffffffffffffffu64, 2u64]
    val c32: [u32] = [0xffffffffu32, 0xffffffffu32, 0xffffffffu32, 0xffffffffu32]
    if hi.sum() != -9223372036854775807: return 14
    if wrap.sum() != 1: return 15
    if c32.sum() != 17179869180: return 16
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
fn unsigned_array_sum_min_max_interpreter() {
    let row = run_interpreter(SOURCE);
    assert_eq!(row, 0, "interpreter failed at row {row}");
}

#[test]
fn unsigned_array_sum_min_max_jit() {
    let row = run_jit(SOURCE);
    assert_eq!(row, 0, "JIT failed at row {row}");
}
