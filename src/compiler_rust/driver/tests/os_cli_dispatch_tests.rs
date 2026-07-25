#![cfg(target_arch = "x86_64")]

use assert_cmd::Command;
use predicates::str::contains;

#[test]
fn cli_os_targets_uses_dedicated_entrypoint() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["os", "targets"]);

    cmd.assert()
        .success()
        .stdout(contains("Supported SimpleOS architectures:"))
        .stdout(contains("x86_64"));
}

#[test]
fn cli_os_build_reports_unknown_architecture_explicitly() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["os", "build", "--arch=definitely-not-real"]);

    cmd.assert()
        .failure()
        .stdout(contains("Error: unknown architecture 'definitely-not-real'"))
        .stdout(contains("simple os targets"));
}
