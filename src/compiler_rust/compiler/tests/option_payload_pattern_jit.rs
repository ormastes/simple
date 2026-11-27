//! Seed JIT: `Some(x)` constructor-pattern payload extraction on a primitive
//! optional (`i64?`) must unbox the payload, exactly like the plain
//! `if val x = opt` form does, and must agree with the tree-walk interpreter.
//!
//! Lane a6dffc9c/p12-6. Bug:
//! doc/08_tracking/bug/jit_some_pattern_payload_shifted_left_3_2026-09-13.md
//!
//! The `T?` primitive lane is TAGGED (`BoxInt` on return, `UnboxInt` on
//! `if val`). The `Some(x)` pattern else-branch used to hand the still-tagged
//! word to an `i64` binding (`7` read back as `56`). It also covers sibling
//! regressions closed by the same re-check: `.?` as a bool call argument and
//! payload 3 (the old nil-sentinel value) surviving `??`/`if val`/`== nil`.
//! `main` returns the number of the first failing row, 0 when all pass.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;

const SOURCE: &str = r#"
fn get(v: i64) -> i64?:
    return v

fn none_i64() -> i64?:
    return None

fn maybe_text(f: bool) -> text?:
    if f:
        return "payload"
    nil

fn is_true(c: bool) -> bool:
    c == true

fn main() -> i64:
    if val Some(a) = get(7):
        if a != 7: return 1
        if a + 1 != 8: return 2
    else:
        return 3
    if val Some(z) = get(0):
        if z != 0: return 4
    else:
        return 5
    if val Some(t) = get(3):
        if t != 3: return 6
    else:
        return 7
    val h = get(100)
    match h:
        case Some(c):
            if c != 100: return 8
        case _:
            return 9
    if val b = get(7):
        if b != 7: return 10
    if get(3) == nil: return 11
    if (get(3) ?? -99) != 3: return 12
    if val Some(q) = none_i64():
        return 13
    if not is_true(maybe_text(true).?): return 14
    if is_true(maybe_text(false).?): return 15
    return 0
"#;

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
fn some_pattern_payload_on_primitive_optional_is_unboxed_on_jit() {
    let interpreted = run_interpreter();
    let jit = run_jit();
    assert_eq!(interpreted, 0, "interpreter control failed at row {interpreted}");
    assert_eq!(jit, 0, "JIT diverged from the interpreter at row {jit}");
}
