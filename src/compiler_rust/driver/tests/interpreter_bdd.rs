use assert_cmd::Command;
use predicates::str::contains;
use std::fs;
use std::os::unix::process::ExitStatusExt;
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

#[test]
fn mutual_recursion_diagnoses_cleanly_instead_of_crashing() {
    // Regression for doc/08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md.
    //
    // Any spec importing `app.io.mod` used to abort with a raw native
    // "fatal runtime error: stack overflow, aborting" (SIGSEGV/core dump)
    // instead of a clean diagnostic. Root cause was two-fold:
    //   1. `src/compiler_rust/lib/std/src/io/fs_helpers.spl` imported
    //      `file_exists` from `infra.file_io` and ALSO defined a local
    //      `pub fn file_exists` of the same name as a "compatibility
    //      alias" that called `exists()`, which itself called the
    //      (now-locally-shadowed) `file_exists` -- unconditional infinite
    //      mutual recursion between `exists()` and `file_exists()`.
    //   2. The interpreter's own recursion-depth safety net
    //      (`push_call_depth` / `STACK_OVERFLOW_DETECTION_ENABLED`)
    //      defaulted to *disabled* in release builds, so this kind of
    //      interpreter-level infinite recursion crashed the whole process
    //      via a genuine native stack overflow instead of returning a
    //      `CompileError::StackOverflow` diagnostic.
    //
    // fs_helpers.spl was fixed to break the cycle (delegate straight to a
    // local `extern fn rt_file_exists` instead of routing through the
    // shadowed import), and `STACK_OVERFLOW_DETECTION_ENABLED` now
    // defaults to `true` in both debug and release builds so that ANY
    // future interpreter-level infinite recursion -- not just this one --
    // diagnoses instead of crashing. This test reproduces the general
    // shape (two functions that call each other forever) with a synthetic
    // fixture, independent of fs_helpers.spl, and asserts the process
    // exits cleanly with a `CompileError::StackOverflow` message rather
    // than aborting.
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("mutual_recursion_spec.spl");
    fs::write(
        &spec,
        r#"use std.spec.*

fn ping(n: i64) -> i64:
    pong(n)

fn pong(n: i64) -> i64:
    ping(n)

describe "mutual recursion":
    it "diagnoses instead of crashing":
        expect(ping(1)).to_equal(1)
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    // Must NOT crash (no SIGSEGV/core dump -> process exits with a normal
    // status code) and must surface a stack-overflow diagnostic rather than
    // silently hanging or reporting an unrelated failure.
    cmd.assert().success().stdout(contains("stack overflow"));
}

#[test]
fn app_io_mod_import_no_longer_stack_overflows() {
    // Exact minimal repro from
    // doc/08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md:
    // any spec importing `app.io.mod` (even a single non-process helper
    // like `file_exists`) used to abort the whole process with a raw
    // native stack overflow ("fatal runtime error: stack overflow,
    // aborting", SIGSEGV/core dump). That crash must be gone: the example
    // itself must now run and report a clean pass.
    //
    // NOTE: this does not assert `.success()` on the overall process exit
    // code. A separate, pre-existing defect (documented in this same bug
    // doc's "How found" section, and reproduced independently via
    // `simple test --no-session-daemon` during this investigation) makes
    // the `simple` CLI's wrapper-level exit code disagree with a clean BDD
    // summary for specs that import `app.io.mod` -- exit code 1 even when
    // stdout reports "N examples, 0 failures". That is a distinct bug in
    // the CLI wrapper's exit-code accounting, not a crash, and not part of
    // this regression (see `src/app/test_runner_new/test_runner_single.spl`,
    // which is out of scope here). This test only asserts the crash is
    // gone and the example result is correct.
    let dir = tempdir().expect("tempdir");
    let spec = dir.path().join("app_io_mod_repro_spec.spl");
    fs::write(
        &spec,
        r#"use std.spec.*
use app.io.mod.{file_exists}

describe "repro":
    it "just calls file_exists from app.io.mod":
        expect(file_exists("/etc/hostname")).to_equal(true)
"#,
    )
    .expect("write fixture");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root()).arg("run").arg(&spec);

    let output = cmd.output().expect("spawn simple run");
    assert!(
        output.status.signal().is_none(),
        "process was killed by a signal (crash) instead of exiting normally: {:?}",
        output.status
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("stack overflow") && !stderr.contains("fatal runtime error"),
        "process reported a native stack overflow instead of a clean result:\nstdout={stdout}\nstderr={stderr}"
    );
    assert!(
        stdout.contains("1 example, 0 failures"),
        "expected a clean single-example pass, got:\nstdout={stdout}\nstderr={stderr}"
    );
}
