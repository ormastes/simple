//! Regression tests for seed compiler bugs fixed 2026-07-16/17:
//!
//! - 86e56ca7867 (hir/lower/expr/mod.rs): qualified `Result.Ok(x)` receivers
//!   route through static-member lowering, which MIR canonicalizes to
//!   `MirInst::ResultOk` even with no explicit `Result` type registration.
//! - d85059513a2 (mir/lower/lowering_expr_ops.rs `lower_short_circuit_logical`):
//!   `x and call()` / `x or call()` must lower to true branching MIR -- the
//!   right operand is only evaluated on the side of the branch that needs it,
//!   and the merge temp is I64 (not BOOL). `and~`/`or~` (AndSuspend/OrSuspend)
//!   keep the old eager (both-operands-always-evaluated) path.

use super::common::*;
use crate::hir::TypeId;
use crate::mir::function::MirFunction;
use crate::mir::{MirInst, Terminator};

/// Find the index of the first block containing a direct `Call` whose target
/// function name matches `name`.
fn block_index_with_call(func: &MirFunction, name: &str) -> Option<usize> {
    func.blocks.iter().position(|b| {
        b.instructions
            .iter()
            .any(|inst| matches!(inst, MirInst::Call { target, .. } if target.name() == name))
    })
}

fn has_call(func: &MirFunction, name: &str) -> bool {
    block_index_with_call(func, name).is_some()
}

// =============================================================================
// #1: Result.Ok end-to-end MIR canonicalization (86e56ca7867)
// =============================================================================

#[test]
fn result_ok_canonicalizes_to_mir_result_ok_instruction() {
    let mir = compile_to_mir("fn make() -> i64:\n    val r = Result.Ok(1)\n    return 0\n").unwrap();
    let has_result_ok = mir
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .any(|i| matches!(i, MirInst::ResultOk { .. }));
    assert!(has_result_ok, "Result.Ok(1) must canonicalize to MirInst::ResultOk in MIR");
}

// =============================================================================
// #6: short-circuit and/or default (non-coverage) MIR lowering (d85059513a2)
// =============================================================================

#[test]
fn short_circuit_and_evaluates_rhs_call_only_in_conditional_block() {
    let mir = compile_to_mir(
        "fn call() -> bool:\n    return true\n\nfn test(x: bool) -> bool:\n    return x and call()\n",
    )
    .unwrap();
    let func = mir.functions.iter().find(|f| f.name == "test").expect("test fn");

    // Entry block must branch (not eagerly fall through to the call).
    let entry = func.block(crate::mir::BlockId(0)).expect("entry block");
    assert!(
        matches!(entry.terminator, Terminator::Branch { .. }),
        "entry block must branch on `x`, got {:?}",
        entry.terminator
    );
    assert!(
        !has_call(func, "call") || block_index_with_call(func, "call") != Some(0),
        "call() must NOT be lowered unconditionally into the entry block"
    );
    let call_block = block_index_with_call(func, "call").expect("call() must appear somewhere in the function");
    assert_ne!(call_block, 0, "call() must live in a conditional (non-entry) block");

    // Merge temp local (__logical_*) must be typed I64, not BOOL.
    let logical_local = func
        .locals
        .iter()
        .find(|l| l.name.starts_with("__logical_"))
        .expect("expected a __logical_* merge temp local");
    assert_eq!(logical_local.ty, TypeId::I64, "short-circuit merge temp must be I64, not BOOL");
}

#[test]
fn short_circuit_or_evaluates_rhs_call_only_in_conditional_block() {
    let mir =
        compile_to_mir("fn call() -> bool:\n    return true\n\nfn test(x: bool) -> bool:\n    return x or call()\n")
            .unwrap();
    let func = mir.functions.iter().find(|f| f.name == "test").expect("test fn");

    let entry = func.block(crate::mir::BlockId(0)).expect("entry block");
    assert!(
        matches!(entry.terminator, Terminator::Branch { .. }),
        "entry block must branch on `x`, got {:?}",
        entry.terminator
    );
    let call_block = block_index_with_call(func, "call").expect("call() must appear somewhere in the function");
    assert_ne!(call_block, 0, "call() must live in a conditional (non-entry) block");

    let logical_local = func
        .locals
        .iter()
        .find(|l| l.name.starts_with("__logical_"))
        .expect("expected a __logical_* merge temp local");
    assert_eq!(logical_local.ty, TypeId::I64, "short-circuit merge temp must be I64, not BOOL");
}

/// Sibling: nested `a and (b or c())` -- the innermost call must still be
/// reachable only through conditional blocks, never the entry block.
#[test]
fn nested_and_or_short_circuit_keeps_innermost_call_conditional() {
    let mir = compile_to_mir(
        "fn c() -> bool:\n    return true\n\nfn test(a: bool, b: bool) -> bool:\n    return a and (b or c())\n",
    )
    .unwrap();
    let func = mir.functions.iter().find(|f| f.name == "test").expect("test fn");

    let entry = func.block(crate::mir::BlockId(0)).expect("entry block");
    assert!(
        matches!(entry.terminator, Terminator::Branch { .. }),
        "entry block must branch on `a`, got {:?}",
        entry.terminator
    );
    let call_block = block_index_with_call(func, "c").expect("c() must appear somewhere in the function");
    assert_ne!(call_block, 0, "c() must never be reachable unconditionally from the entry block");

    // Both the outer (a and ...) and inner (b or c()) merges allocate their
    // own __logical_* temp, all I64.
    let logical_locals: Vec<_> = func.locals.iter().filter(|l| l.name.starts_with("__logical_")).collect();
    assert!(
        logical_locals.len() >= 2,
        "nested and/or must allocate a merge temp per short-circuit level, got {}",
        logical_locals.len()
    );
    for local in logical_locals {
        assert_eq!(local.ty, TypeId::I64, "every short-circuit merge temp must be I64");
    }
}

/// `and~`/`or~` (AndSuspend/OrSuspend, the suspension await-forms) must keep
/// the OLD eager path: both operands lowered unconditionally, no branch
/// introduced for this expression, call() reachable straight from the entry
/// block.
#[test]
fn and_suspend_keeps_eager_unconditional_evaluation() {
    let mir = compile_to_mir(
        "fn call() -> bool:\n    return true\n\nfn test(x: bool) -> bool:\n    return x and~ call()\n",
    )
    .unwrap();
    let func = mir.functions.iter().find(|f| f.name == "test").expect("test fn");

    let call_block = block_index_with_call(func, "call").expect("call() must appear somewhere in the function");
    assert_eq!(
        call_block, 0,
        "and~ (AndSuspend) must keep the eager path: call() unconditionally in the entry block"
    );
    assert!(
        func.locals.iter().all(|l| !l.name.starts_with("__logical_")),
        "and~ must not allocate a short-circuit merge temp (eager path has no branch/merge)"
    );
}

#[test]
fn or_suspend_keeps_eager_unconditional_evaluation() {
    let mir =
        compile_to_mir("fn call() -> bool:\n    return true\n\nfn test(x: bool) -> bool:\n    return x or~ call()\n")
            .unwrap();
    let func = mir.functions.iter().find(|f| f.name == "test").expect("test fn");

    let call_block = block_index_with_call(func, "call").expect("call() must appear somewhere in the function");
    assert_eq!(
        call_block, 0,
        "or~ (OrSuspend) must keep the eager path: call() unconditionally in the entry block"
    );
    assert!(
        func.locals.iter().all(|l| !l.name.starts_with("__logical_")),
        "or~ must not allocate a short-circuit merge temp (eager path has no branch/merge)"
    );
}
