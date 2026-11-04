//! std.spec `skip(...)` only prints, so the compiled lane must count it via
//! `rt_bdd_note_skip` for the verdict's `skipped=` to match the interpreter.
//! Bug: doc/08_tracking/bug/seed_jit_spec_files_never_jit_2026-11-04.md

use super::common::compile_to_mir;
use crate::mir::{CallTarget, MirInst};

#[test]
fn skip_statement_counts_and_keeps_call() {
    let src = "fn skip(name: text, reason: text):\n    print name\n\nfn run():\n    skip(\"a\", \"b\")\n";
    let mir = compile_to_mir(src).expect("fixture lowers");
    let f = mir.functions.iter().find(|f| f.name == "run").expect("run fn");
    let calls: Vec<String> = f
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter_map(|i| match i {
            MirInst::Call { target, .. } => Some(format!("{target:?}")),
            _ => None,
        })
        .collect();
    let note = CallTarget::from_name("rt_bdd_note_skip");
    assert!(calls.iter().any(|c| *c == format!("{note:?}")), "no rt_bdd_note_skip in {calls:?}");
    assert!(calls.iter().any(|c| c.contains("skip") && !c.contains("rt_bdd")), "skip body call dropped: {calls:?}");
}
