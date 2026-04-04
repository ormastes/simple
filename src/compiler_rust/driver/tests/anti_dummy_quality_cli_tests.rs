#![cfg(target_arch = "x86_64")]

use assert_cmd::Command;
use predicates::str::contains;
use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;

fn project_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().unwrap().parent().unwrap().to_path_buf()
}

#[test]
fn lint_flags_boolean_wrapper_assertion() {
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("bad_quality_spec.spl");
    fs::write(
        &spec,
        "describe \"x\":\n    it \"y\":\n        expect(code != 0).to_equal(true)\n",
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("lint").arg(&spec);

    cmd.assert().failure().stdout(contains("SSPEC006"));
}

#[test]
fn lint_flags_explicit_placeholder_impl() {
    let dir = tempdir().expect("tempdir");
    let source = dir.path().join("placeholder_impl.spl");
    fs::write(
        &source,
        "fn answer(x: i64) -> i64:\n    pass_todo(\"implement answer\")\n",
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("lint").arg(&source);

    cmd.assert().failure().stdout(contains("STUB003"));
}

#[test]
fn verify_quality_fails_on_placeholder_test() {
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("placeholder_spec.spl");
    fs::write(
        &spec,
        "describe \"x\":\n    it \"y\":\n        pass_todo\n",
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root())
        .arg("verify")
        .arg("quality")
        .arg(&spec);

    cmd.assert().failure().stdout(contains("SSPEC002"));
}

#[test]
fn verify_quality_passes_clean_fixture() {
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("good_spec.spl");
    fs::write(
        &spec,
        "describe \"x\":\n    it \"y\":\n        expect(1 + 1).to_equal(2)\n",
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root())
        .arg("verify")
        .arg("quality")
        .arg(&spec);

    cmd.assert().success().stdout(contains("Verify quality passed"));
}
