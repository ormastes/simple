//! `bool` parameters use the language's presence conversion on every engine.
//!
//! The tree-walk interpreter already applies this rule in `arg_binding.rs`,
//! while the Cranelift call ABI used to truncate each non-bool argument to the
//! callee's `i8` slot. That made `0` false, `nil` true, and pointer payloads
//! depend on their low byte. The case number returned by `main` identifies the
//! first boundary row that differs.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn takes_bool(value: bool) -> bool:
    value

fn none_i64() -> i64?:
    nil

fn some_zero() -> i64?:
    Some(0)

fn main() -> i64:
    if takes_bool(false): return 1
    if not takes_bool(true): return 2
    if not takes_bool(0): return 3
    if not takes_bool(1): return 4
    if not takes_bool("present"): return 5
    if takes_bool(nil): return 6
    if takes_bool(none_i64()): return 7
    if not takes_bool(some_zero()): return 8
    return 0
"#;

fn run_interpreter() -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source)
        .parse()
        .expect("bool-boundary source must parse for interpreter");
    interpreter::evaluate_module(&module.items).expect("bool-boundary source must run in interpreter")
}

fn run_jit() -> i64 {
    let ast = Parser::new(SOURCE)
        .parse()
        .expect("bool-boundary source must parse for JIT");
    let hir_module = hir::lower(&ast).expect("bool-boundary source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("bool-boundary source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("bool-boundary MIR must compile");
    unsafe { jit.call_i64_void("main").expect("bool-boundary main must execute") }
}

#[test]
fn bool_parameter_presence_conversion_matches_interpreter_and_native_jit() {
    let interpreted = run_interpreter();
    let native = run_jit();
    assert_eq!(interpreted, 0, "interpreter control failed at case {interpreted}");
    assert_eq!(native, interpreted as i64, "native/JIT diverged at case {native}");
}
