//! Regression pin for `seed_run_passing_assert_exit139_2026-11-09` (P2).
//!
//! `simple run` on
//!
//! ```simple
//! fn main():
//!     assert(1 == 1)
//!     print("after assert")
//! ```
//!
//! segfaulted (exit 139) on the 2026-11-04 deployed seed. The
//! statement-position call spelling `assert(COND[, MSG])` must lower to the
//! assertion statement (HIR `HirStmt::Assert`; interpreter `assert` builtin
//! arm) — never to a bare call that can bind libc's `__assert` or an
//! unresolved JIT external and jump to a bad address on a *passing* assert.
//!
//! Absorber: PR #7597 (merge 9e7e7a526edb, 2026-11-07), which added both the
//! HIR statement desugar (`hir/lower/stmt_lowering.rs`) and the interpreter
//! parity arm (`interpreter_call/builtins.rs`). The 2026-11-04 seed binary
//! predates it.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module)
        .expect("module must JIT-compile (a bare `assert` external must not be emitted)");
    unsafe { jit.call_i64_void("main").expect("main must execute without segfault") }
}

/// Exact shape from the bug row: a passing `assert(...)` call in statement
/// position followed by more work. Pre-fix this emitted a call to the
/// unresolved `assert` external and crashed with exit 139; now it is a no-op
/// and execution continues.
#[test]
fn passing_call_form_assert_is_a_no_op_under_jit() {
    let src = "fn main() -> i64:\n    assert(1 == 1)\n    return 7\n";
    assert_eq!(run(src), 7);
}

/// The two-argument call spelling with a literal message must behave the
/// same way when the condition holds.
#[test]
fn passing_call_form_assert_with_message_is_a_no_op_under_jit() {
    let src = "fn main() -> i64:\n    assert(2 > 1, \"must hold\")\n    return 3\n";
    assert_eq!(run(src), 3);
}
