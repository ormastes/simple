//! A module-level `fn` named like a cast builtin (`f32`, `i32`, `int`, ...)
//! is the function the program calls, on the JIT as in the interpreter.
//!
//! The interpreter lets a user module-level `fn` win over a builtin of the
//! same name (`builtin_wins_over_user_fn`, only `exit`/`dprint`/`panic` are
//! unshadowable; doc/08_tracking/bug/module_fn_shadowed_by_builtin_name_2026-08-21.md).
//! HIR lowering turned every one-argument `f32(x)`/`i32(x)` call into a cast
//! before looking at user functions, so the JIT printed `17.0` where the
//! interpreter printed `18`.
//! Bug: doc/08_tracking/bug/jit_user_fn_named_like_primitive_calls_cast_2026-11-24.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run_main(src: &str) -> i64 {
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn user_fn_named_like_a_cast_is_called() {
    let src = "fn f32(x: i64) -> i64:
    x + 1

fn i32(x: i64) -> i64:
    x + 2

fn int(x: i64) -> i64:
    x + 3

fn main() -> i64:
    f32(17) + i32(17) * 100 + int(17) * 10000
";
    assert_eq!(run_main(src), 18 + 19 * 100 + 20 * 10000);
}

#[test]
fn cast_call_without_a_user_fn_still_casts() {
    // No user `fn i32`/`fn int`: the call form is the builtin conversion.
    let src = "fn main() -> i64:
    i32(7) + int(\"35\")
";
    assert_eq!(run_main(src), 42);
}
