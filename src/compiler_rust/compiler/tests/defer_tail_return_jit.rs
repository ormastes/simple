//! MIR lowering: a function with `defer` must return its implicit tail value.
//!
//! `lower_function` lowered the body, then `emit_deferred_blocks`, then read
//! `last_expr_value` for the implicit return. Lowering the deferred statements
//! overwrote `last_expr_value`, so the function returned the deferred call's
//! result (`nil` -> 0, or a null struct handle -> SIGSEGV on the first field
//! read) instead of its tail expression. The interpreter was correct.
//! Found behind the JIT `dynlib` fix: `SimpleHttpServer.handle_connection_on_owner_v1`
//! (`defer self.admission.release()`) crashed every JIT live-socket probe.
//! doc/08_tracking/bug/seed_mir_defer_clobbers_implicit_tail_return_2026-11-06.md

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
fn defer_keeps_implicit_tail_return_value() {
    let source = r#"
fn cleanup() -> i64:
    7

fn with_defer() -> i64:
    defer cleanup()
    val r = 41 + 1
    r

fn with_two_defers(x: i64) -> i64:
    defer cleanup()
    defer cleanup()
    x * 2

fn with_explicit_return() -> i64:
    defer cleanup()
    return 5

fn main() -> i64:
    if with_defer() != 42:
        return 1
    if with_two_defers(21) != 42:
        return 2
    if with_explicit_return() != 5:
        return 3
    0
"#;
    assert_eq!(run(source), 0);
}
