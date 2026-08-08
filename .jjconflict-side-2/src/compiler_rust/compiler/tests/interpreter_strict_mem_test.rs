//! Plan M5 (strict interpreter mode) — gate + uninit-read trap.
//! See doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md
//!
//! `strict_mem_enabled()` is backed by a process-wide `OnceLock<bool>`
//! (mirrors `heap.rs` `ATTR_ENABLED`), so it can only be switched on once per
//! test binary. Everything that must observe the *disabled* gate runs first,
//! in one test function, before `strict_mem_enable()` is ever called — that
//! ordering is why this file uses a single `#[test]` rather than several.

use simple_compiler::interpreter;
use simple_parser::Parser;

fn evaluate(source: &str) -> Result<i32, simple_compiler::error::CompileError> {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = Parser::new(source).parse().unwrap();
    let result = interpreter::evaluate_module(&module.items);
    result
}

const UNINIT_READ_SRC: &str = "fn main() -> i32:\n    let x: i32\n    return x\n";

const ASSIGN_THEN_READ_SRC: &str = "fn main() -> i32:\n    var x: i32\n    x = 7\n    return x\n";

#[test]
fn strict_mem_gate_and_uninit_read_trap() {
    // 1. Gate OFF (default, pre-existing behavior): an initializer-less
    //    `let` read does NOT raise the strict-mem trap. It still fails
    //    today (E1001 undefined-variable, or a shadow-miss per the design
    //    doc) but never with the strict-mem message, since the gate has
    //    never been enabled in this process yet.
    assert!(
        !simple_compiler::value::strict_mem_enabled(),
        "gate must default OFF before any enable call"
    );
    let normal_result = evaluate(UNINIT_READ_SRC);
    if let Err(e) = &normal_result {
        assert!(
            !e.to_string().contains("strict-mem"),
            "normal mode must never raise the strict-mem trap, got: {e}"
        );
    }

    // 2. Enable strict mode (test-only programmatic hook, mirrors
    //    mem_attr_enable()). From here on the gate is ON for the rest of
    //    this process.
    simple_compiler::value::strict_mem_enable();
    assert!(simple_compiler::value::strict_mem_enabled());

    // 3. Strict mode: reading an initializer-less `let` before any
    //    assignment raises the strict-mem trap, naming the variable.
    let strict_result = evaluate(UNINIT_READ_SRC);
    let err = strict_result.expect_err("strict mode must trap the uninitialized read");
    let msg = err.to_string();
    assert!(
        msg.contains("strict-mem: read of uninitialized x"),
        "expected strict-mem uninit trap naming `x`, got: {msg}"
    );

    // 4. Strict mode: assignment before the read clears the trap — the
    //    binding behaves exactly as a normal initialized variable.
    let assigned_result = evaluate(ASSIGN_THEN_READ_SRC);
    assert_eq!(assigned_result.unwrap(), 7);
}
