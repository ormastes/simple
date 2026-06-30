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
fn bdd_matcher_pass_after_failure_keeps_example_failed() {
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("bdd_failure_persistence_spec.spl");
    fs::write(
        &spec,
        r#"describe "bdd matcher persistence":
    it "keeps first failure":
        expect("deliberate").to_equal("failure")
        expect(1).to_equal(1)
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    cmd.assert()
        .success()
        .stdout(contains("expected deliberate to equal failure"))
        .stdout(contains("1 example, 1 failure"));
}

#[test]
fn bdd_matcher_passes_on_falsy_call_result() {
    // Regression: `expect(<call returning 0/false/"">).to_equal(<same falsy>)`
    // must PASS. The hollow-call truthiness guard previously marked the falsy
    // call result failed, and after the "pass does not clear prior failure"
    // change that pre-failure was never cleared -> false RED.
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("bdd_falsy_call_spec.spl");
    fs::write(
        &spec,
        r#"fn ret_zero() -> i32:
    0
fn ret_false() -> bool:
    false
describe "bdd falsy call result":
    it "zero call equals zero":
        expect(ret_zero()).to_equal(0)
    it "false call equals false":
        expect(ret_false()).to_equal(false)
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    cmd.assert().success().stdout(contains("2 examples, 0 failures"));
}

#[test]
fn bdd_bare_falsy_call_without_matcher_still_fails() {
    // The hollow-call guard must still catch a bare `expect(<falsy call>)` with
    // no matcher chain (no silent false-green).
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("bdd_hollow_call_spec.spl");
    fs::write(
        &spec,
        r#"fn ret_zero() -> i32:
    0
describe "bdd hollow call":
    it "bare falsy call fails":
        expect(ret_zero())
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    cmd.assert().success().stdout(contains("1 example, 1 failure"));
}

#[test]
fn bdd_enum_method_in_nested_call_context() {
    // Regression: calling an enum method on an enum value returned by a nested
    // call (e.g. `t.arch().to_string()`) failed in chained-call position with
    // "method 'to_string' not found on value of type enum in nested call
    // context", even though the same chain works in a plain function body.
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("bdd_enum_nested_spec.spl");
    fs::write(
        &spec,
        r#"enum Color:
    Red
    Green
    fn label() -> text:
        match self:
            Red: "red"
            Green: "green"
class Box:
    pass_dn
impl Box:
    static fn create() -> Box:
        Box()
    fn color() -> Color:
        Color.Green
describe "enum method in nested call":
    it "dispatches to_string-style method on nested enum result":
        val b = Box.create()
        expect(b.color().label()).to_equal("green")
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    cmd.assert().success().stdout(contains("1 example, 0 failures"));
}
