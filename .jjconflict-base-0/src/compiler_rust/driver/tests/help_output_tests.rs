#![cfg(target_arch = "x86_64")]

use assert_cmd::Command;
use predicates::str::contains;

#[test]
fn cli_help_lists_examples_check_usage() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.arg("--help");

    cmd.assert()
        .success()
        .stderr(contains(
            "simple examples-check [path] [--compile|--run] [--timeout <secs>]",
        ))
        .stderr(contains("Validate examples one by one with per-file isolation"));
}
