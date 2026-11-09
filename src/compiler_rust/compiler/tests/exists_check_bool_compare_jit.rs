//! `x.? == true` / `x.? == false` are nil-safe and match pure Simple on the
//! seed's JIT lane (the default `simple run` engine), not only the
//! interpreter. Owner decision 2026-11-09; bug
//! doc/08_tracking/bug/seed_optional_query_comparison_divergence_2026-08-16.md.
//!
//! Expected bits come from the native stage2 (pure Simple) probe of the same
//! program on 2026-11-09: nil -> neither literal, present text -> neither,
//! `bool?` false -> `== false`, `bool?` true -> `== true`.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn main() -> i64:
    val a: text? = nil
    val b: text? = "x"
    val c: bool? = false
    val d: bool? = true
    val e: bool? = nil
    var bits = 0
    if a.? == false: bits = bits + 1
    if a.? == true: bits = bits + 2
    if b.? == false: bits = bits + 4
    if b.? == true: bits = bits + 8
    if c.? == false: bits = bits + 16
    if c.? == true: bits = bits + 32
    if d.? == false: bits = bits + 64
    if d.? == true: bits = bits + 128
    if e.? == false: bits = bits + 256
    if e.? == true: bits = bits + 512
    if c.? != false: bits = bits + 1024
    if e.? != true: bits = bits + 2048
    if false == c.?: bits = bits + 4096
    return bits
"#;

const PURE_SIMPLE_BITS: i64 = 16 + 128 + 2048 + 4096;

fn run_interpreter() -> i64 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("source must run in interpreter") as i64
}

fn run_jit() -> i64 {
    let ast = Parser::new(SOURCE).parse().expect("source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn exists_check_bool_compare_matches_pure_simple_on_jit() {
    assert_eq!(run_jit(), PURE_SIMPLE_BITS);
}

#[test]
fn exists_check_bool_compare_matches_pure_simple_on_interpreter() {
    assert_eq!(run_interpreter(), PURE_SIMPLE_BITS);
}
