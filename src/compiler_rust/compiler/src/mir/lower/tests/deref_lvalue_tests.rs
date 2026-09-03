//! Regression tests for deref-lvalue MIR lowering.
//!
//! `*ptr = value` had no arm in `lower_lvalue` (mir/lower/lowering_gpu.rs), so
//! it fell into the catch-all and failed with
//! `Unsupported HIR construct: complex lvalue: Deref(...)`. On the JIT path
//! that silently dropped the whole module to the interpreter, which is why no
//! value-asserting backend test caught it; a freestanding kernel (the riscv64
//! WM closure) has no interpreter to fall back to, so it was a hard
//! native-build failure there.
//!
//! These tests assert on the LOWERING RESULT, not on a runtime value, so they
//! are genuinely RED before the fix.
//!
//! See doc/08_tracking/bug/
//! deref_assign_after_multiline_call_parsed_as_multiply_2026-09-01.md.

use super::common::*;
use crate::mir::MirInst;

const DEREF_ASSIGN: &str = "\
fn store(p: rawptr<i64>, v: i64):
    *p = v
";

#[test]
fn deref_assignment_lowers_to_mir() {
    let result = compile_to_mir(DEREF_ASSIGN);
    match result {
        Ok(_) => {}
        Err(err) => panic!("deref assignment must lower to MIR, got: {:?}", err),
    }
}

#[test]
fn deref_assignment_emits_a_store() {
    let mir = compile_to_mir(DEREF_ASSIGN).expect("deref assignment must lower to MIR");
    let store = mir
        .functions
        .iter()
        .find(|f| f.name == "store")
        .expect("`store` function must be present in the lowered module");
    assert!(
        store
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .any(|inst| matches!(inst, MirInst::Store { .. })),
        "`*p = v` must lower to a Store through the pointer's value"
    );
}

#[test]
fn deref_assignment_after_multiline_call_lowers_to_mir() {
    // The exact shape at src/os/kernel/arch/riscv64/interrupt.spl:347-350:
    // a call whose argument list spans lines, immediately followed by two
    // deref assignments. Exercises the parser fix and the MIR fix together.
    let src = "\
fn store2(p: rawptr<i64>, q: rawptr<i64>, v: i64):
    val s = compute(
        v)
    *p = s
    *q = s

fn compute(v: i64) -> i64:
    v
";
    let result = compile_to_mir(src);
    assert!(
        result.is_ok(),
        "deref assignments after a multi-line call must lower to MIR, got: {:?}",
        result.err()
    );
}
