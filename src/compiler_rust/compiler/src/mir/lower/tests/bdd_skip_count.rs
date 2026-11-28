//! std.spec `skip(...)` only prints, so the compiled lane must count it via
//! `rt_bdd_note_skip` for the verdict's `skipped=` to match the interpreter.
//! Bug: doc/08_tracking/bug/seed_jit_spec_files_never_jit_2026-11-04.md
//!
//! Since seed_same_name_fn_binding_2026-11-27 a DSL name that the module being
//! lowered declares itself is that module's own function and is NOT counted;
//! the framework `skip` must therefore come from outside the module (as it does
//! via `use std.spec`), not be defined in the fixture.

use super::common::compile_to_mir;
use crate::mir::{CallTarget, MirInst};

fn run_calls(src: &str) -> Vec<String> {
    let mir = compile_to_mir(src).expect("fixture lowers");
    let f = mir.functions.iter().find(|f| f.name == "run").expect("run fn");
    f.blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter_map(|i| match i {
            MirInst::Call { target, .. } => Some(format!("{target:?}")),
            _ => None,
        })
        .collect()
}

fn note_skip() -> String {
    format!("{:?}", CallTarget::from_name("rt_bdd_note_skip"))
}

#[test]
fn skip_statement_counts_and_keeps_call() {
    // `extern fn` stands in for the framework `skip` imported from std.spec:
    // it is declared but not an own `fn` of the module.
    let calls = run_calls("extern fn skip(name: text, reason: text)\n\nfn run():\n    skip(\"a\", \"b\")\n");
    assert!(calls.contains(&note_skip()), "no rt_bdd_note_skip in {calls:?}");
    assert!(calls.iter().any(|c| c.contains("skip") && !c.contains("rt_bdd")), "skip body call dropped: {calls:?}");
}

#[test]
fn module_declared_skip_is_an_ordinary_call_and_not_counted() {
    let calls = run_calls("fn skip(name: text, reason: text):\n    print name\n\nfn run():\n    skip(\"a\", \"b\")\n");
    assert!(!calls.contains(&note_skip()), "user-declared skip must not be counted: {calls:?}");
    assert!(calls.iter().any(|c| c.contains("skip")), "skip call dropped: {calls:?}");
}
