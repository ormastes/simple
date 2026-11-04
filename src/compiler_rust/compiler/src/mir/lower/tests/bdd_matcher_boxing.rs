//! BDD matcher operands must cross into `rt_bdd_expect_*_rv` as tagged
//! RuntimeValues. A raw scalar compared against a tagged `any` value made
//! equal values fail under the JIT ("Expected nil to equal 0").
//! Bug: doc/08_tracking/bug/seed_jit_spec_files_never_jit_2026-11-04.md

use super::common::compile_to_mir;
use crate::mir::{CallTarget, MirInst};

#[test]
fn expect_eq_boxes_typed_int_operands() {
    let mir = compile_to_mir("fn check(n: i64):\n    expect(n).to_equal(0)\n").expect("fixture lowers");
    let f = mir.functions.iter().find(|f| f.name == "check").expect("check fn");
    let insts: Vec<_> = f.blocks.iter().flat_map(|b| b.instructions.iter()).collect();
    let boxed: std::collections::HashSet<_> = insts
        .iter()
        .filter_map(|i| match i {
            MirInst::BoxInt { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect();
    let args = insts
        .iter()
        .find_map(|i| match i {
            MirInst::Call { target, args, .. } if target == &CallTarget::from_name("rt_bdd_expect_eq_rv") => {
                Some(args.clone())
            }
            _ => None,
        })
        .expect("rt_bdd_expect_eq_rv call");
    assert_eq!(args.len(), 2);
    for a in &args {
        assert!(boxed.contains(a), "operand {a:?} reached rt_bdd_expect_eq_rv raw");
    }
}

/// `expect(p.?).to_equal(true)` asks about presence, as the interpreter's
/// `eval_assertion_operand` does; value-position `.?` would pass the payload.
#[test]
fn expect_eq_exists_check_operand_is_presence_bool() {
    let mir = compile_to_mir("fn check(p: i64?):\n    expect(p.?).to_equal(true)\n").expect("fixture lowers");
    let f = mir.functions.iter().find(|f| f.name == "check").expect("check fn");
    let has_present = f.blocks.iter().flat_map(|b| b.instructions.iter()).any(|i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_is_present"))
    });
    assert!(has_present, "expect(p.?) must lower to the rt_is_present predicate");
}
