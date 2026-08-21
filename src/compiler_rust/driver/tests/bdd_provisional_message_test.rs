//! Regression test for
//! doc/08_tracking/bug/spec_runner_provisional_truthy_message_clobbers_real_failure_2026-08-21.md
//!
//! A PROVISIONAL "expected subject to be truthy" message (raised by any falsy
//! `expect(...)` subject) must never replace a REAL matcher failure that was
//! already recorded earlier in the same example.
//!
//! Fixture-driven: the deliberately-failing spec runs in a child process and we
//! assert on the CAPTURED runner output, so nothing in the repo stays red.

use std::process::Command;

fn run_spec(source: &str) -> String {
    let dir = tempfile::tempdir().expect("temp dir");
    let spec = dir.path().join("provisional_clobber_spec.spl");
    std::fs::write(&spec, source).expect("write spec");

    // The runner dispatches to `src/app/test_runner_new/**`, resolved relative to
    // the CWD, so the child must run from the repo root (this crate lives at
    // <repo>/src/compiler_rust/driver).
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

    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn real_to_equal_failure_survives_a_later_falsy_expect() {
    // First matcher fails for real; afterwards the example runs falsy-subject
    // expects (0, "", false) that each raise a provisional truthy message.
    let output = run_spec(
        r#"
describe "provisional clobber":
    it "reports the real to_equal failure":
        expect("fetch-3").to_equal("fetch-2")
        expect(0).to_equal(0)
        expect("").to_equal("")
        expect(false).to_be(false)
"#,
    );

    assert!(
        output.contains("expected fetch-3 to equal fetch-2"),
        "real to_equal failure text missing from runner output:\n{output}"
    );
    assert!(
        !output.contains("expected subject to be truthy"),
        "provisional truthy message clobbered the real failure:\n{output}"
    );
}

#[test]
fn a_bare_falsy_expect_still_reports_the_provisional_message() {
    // The provisional slot must still be PROMOTED when there is no real failure,
    // otherwise the fix would silence hollow-expect reporting.
    let output = run_spec(
        r#"
describe "bare falsy expect":
    it "fails with the truthy message":
        expect(false)
"#,
    );

    assert!(
        output.contains("expected subject to be truthy"),
        "bare falsy expect lost its provisional message:\n{output}"
    );
}
