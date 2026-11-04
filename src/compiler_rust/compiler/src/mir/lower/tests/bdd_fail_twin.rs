//! std.spec `fail(msg)` is an interpreter builtin that wins over any Simple
//! definition; the compiled lane must lower it to `rt_bdd_fail_rv` instead of
//! an unresolved call to `fail`.
//! Bug: doc/08_tracking/bug/seed_jit_spec_files_never_jit_2026-11-04.md

use super::common::compile_to_mir;
use crate::mir::{CallTarget, MirInst};

fn calls_in(src: &str, fname: &str) -> Vec<String> {
    let mir = compile_to_mir(src).expect("fixture lowers");
    let f = mir.functions.iter().find(|f| f.name == fname).expect("fn");
    f.blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .filter_map(|i| match i {
            MirInst::Call { target, .. } => Some(format!("{target:?}")),
            _ => None,
        })
        .collect()
}

#[test]
fn fail_statement_lowers_to_runtime_twin() {
    for name in ["fail", "fail_assertion", "fail_test"] {
        let src = format!("fn run(n: text):\n    {name}(\"missing \" + n)\n");
        let calls = calls_in(&src, "run");
        let twin = format!("{:?}", CallTarget::from_name("rt_bdd_fail_rv"));
        assert!(calls.iter().any(|c| *c == twin), "{name}: no rt_bdd_fail_rv in {calls:?}");
        assert!(
            !calls.iter().any(|c| c.contains(&format!("\"{name}\""))),
            "{name}: unresolved call kept: {calls:?}"
        );
    }
}
