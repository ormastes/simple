//! A placeholder lambda (`_1 + 1`) passed to a user fn parameter must compute
//! the same value as the explicit lambda under the JIT, or the module must be
//! refused (deferred to the interpreter) — never a silently wrong value.
//!
//! Pre-fix: `apply(_1 + 1, 4)` returned 40 (placeholder params defaulted to ANY
//! while the typed callee passed raw i64), and `call_once(_1 + 1)` returned the
//! tagged 11 (88) because the untyped indirect call in `call_once` was never
//! checked (it builds no closure itself).
//! doc/08_tracking/bug/placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn lower(source: &str) -> mir::MirModule {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower_lenient(&ast).expect("source must lower to HIR");
    mir::lower_to_mir(&hir_module).expect("source must lower to MIR")
}

#[test]
fn typed_fn_param_placeholder_lambda_computes_explicit_value() {
    let source = r#"
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)

fn main() -> i64:
    if apply(_1 + 1, 4) != 5: return 1
    if apply(_1 * 3, 4) != 12: return 2
    if apply(_ + 1, 4) != 5: return 3
    if apply(\v: v + 1, 4) != 5: return 4
    0
"#;
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&lower(source)).expect("typed callback boundary must JIT-compile");
    assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 0);
}

#[test]
fn untyped_callee_indirect_call_is_refused_not_miscompiled() {
    let source = r#"
fn call_once(f: any) -> any:
    return f(10)

fn main() -> i64:
    if call_once(_1 + 1) != 11: return 1
    0
"#;
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    match jit.compile_module(&lower(source)) {
        Err(_) => {}
        Ok(()) => assert_eq!(unsafe { jit.call_i64_void("main").expect("main must execute") }, 0),
    }
}
