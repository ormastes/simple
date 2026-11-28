//! Calling a value that is statically a tuple/unit is a compile error in MIR
//! lowering instead of an indirect call through a non-pointer (JIT SIGSEGV).
//! `pass(4)` in expression position parses as `()(4)`, which is how the bug
//! was found.
//! Bug: seed_jit_call_to_function_named_pass_segfaults_2026-11-28.

use std::collections::HashSet;
use std::fs;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};

fn lower(main: &str) -> Result<mir::MirModule, String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, main).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .map_err(|e| e.to_string())?;
    let hir_module = hir::lower(&module).map_err(|e| e.to_string())?;
    mir::lower_to_mir(&hir_module).map_err(|e| e.to_string())
}

fn assert_not_callable(src: &str) {
    let err = lower(src).expect_err("calling a tuple value must not lower");
    assert!(err.contains("is not callable"), "unexpected error: {err}");
}

#[test]
fn calling_pass_in_expression_position_is_a_compile_error() {
    assert_not_callable("fn main() -> i64:\n    val r = pass(4)\n    0\n");
}

#[test]
fn calling_a_unit_literal_is_a_compile_error() {
    assert_not_callable("fn main() -> i64:\n    val r = ()(4)\n    0\n");
}

#[test]
fn calling_a_tuple_local_is_a_compile_error() {
    assert_not_callable("fn main() -> i64:\n    val u = (1, 2)\n    val r = u(4)\n    0\n");
}

#[test]
fn calling_a_function_value_still_works() {
    let mir_module = lower("fn add1(o: i64) -> i64:\n    o + 1\n\nfn main() -> i64:\n    val f = add1\n    f(4)\n")
        .expect("function value call lowers");
    let mut jit = JitCompiler::new_static().expect("JIT");
    jit.compile_module(&mir_module).expect("JIT compile");
    assert_eq!(unsafe { jit.call_i64_void("main").expect("run") }, 5);
}

fn run(src: &str) -> i64 {
    let mir_module = lower(src).expect("callable value call lowers");
    let mut jit = JitCompiler::new_static().expect("JIT");
    jit.compile_module(&mir_module).expect("JIT compile");
    unsafe { jit.call_i64_void("main").expect("run") }
}

#[test]
fn callable_shapes_are_not_rejected() {
    // capturing lambda
    assert_eq!(
        run("fn main() -> i64:\n    val k = 10\n    val f = \\x: x + k\n    f(4)\n"),
        14
    );
    // function-typed parameter
    assert_eq!(
        run("fn apply(f: fn(i64) -> i64, v: i64) -> i64:\n    f(v)\n\nfn add1(o: i64) -> i64:\n    o + 1\n\nfn main() -> i64:\n    apply(add1, 4)\n"),
        5
    );
    // immediately invoked parenthesised lambda
    assert_eq!(run("fn main() -> i64:\n    (\\x: x * 2)(4)\n"), 8);
    // call through a tuple element
    assert_eq!(
        run("fn add1(o: i64) -> i64:\n    o + 1\n\nfn main() -> i64:\n    val pair = (add1, 3)\n    val f = pair.0\n    f(4)\n"),
        5
    );
}
