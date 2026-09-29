//! Regression coverage for
//! doc/08_tracking/bug/interpreter_pending_skip_dsl_intercept_bypasses_spl_body_2026-08-07.md.
//!
//! `pending` and `pending_it` are BDD marker fallbacks only.  A Simple
//! definition with either name must win, just as the nearby `step` DSL does.

use std::process::Command;

fn run_spec(source: &str) -> (bool, String) {
    let dir = tempfile::tempdir().expect("temp dir");
    let spec = dir.path().join("pending_dsl_dispatch_spec.spl");
    std::fs::write(&spec, source).expect("write spec");
    let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .expect("repo root")
        .to_path_buf();
    let out = Command::new(env!("CARGO_BIN_EXE_simple"))
        .current_dir(&repo_root)
        .arg("test")
        .arg(&spec)
        .output()
        .expect("run simple test");
    (
        out.status.success(),
        format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
        ),
    )
}

#[test]
fn user_pending_names_reach_their_simple_bodies() {
    let (success, output) = run_spec(
        r#"
fn pending(name: text) -> i64:
    17

fn pending_it(name: text) -> i64:
    23

describe "pending dispatch":
    it "uses the user pending function":
        expect(pending("must execute")).to_equal(17)
    it "uses the user pending_it function":
        expect(pending_it("must execute")).to_equal(23)
"#,
    );

    assert!(success, "user DSL spec failed:\n{output}");

    assert!(
        output.contains("✓ uses the user pending function"),
        "user pending body was bypassed:\n{output}"
    );
    assert!(
        output.contains("✓ uses the user pending_it function"),
        "user pending_it body was bypassed:\n{output}"
    );
    assert!(
        !output.contains("○ must execute (skipped)"),
        "fallback marker recorded a spurious skipped result:\n{output}"
    );
}

#[test]
fn unowned_pending_remains_a_bdd_marker() {
    let (success, output) = run_spec(
        r#"
describe "pending fallback":
    pending("unowned marker")
    pending_it("unowned alias")
"#,
    );

    assert!(success, "unowned marker spec failed:\n{output}");
    assert!(
        output.contains("○ unowned marker (skipped)"),
        "unowned pending no longer uses the BDD marker fallback:\n{output}"
    );
    assert!(
        output.contains("○ unowned alias (skipped)"),
        "unowned pending_it no longer uses the BDD marker fallback:\n{output}"
    );
}
