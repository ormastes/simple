use assert_cmd::Command;
use predicates::prelude::PredicateBooleanExt;
use predicates::str::{contains, is_empty};

#[test]
fn run_help_is_usage_not_a_source_filename() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["run", "--help"]);

    cmd.assert()
        .success()
        .stderr(contains("Usage: simple run <file.spl> [args...]").and(contains("Cannot read \"--help\"").not()));
}

#[test]
fn run_short_help_is_usage() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["run", "-h"]);

    cmd.assert()
        .success()
        .stderr(contains("Usage: simple run <file.spl> [args...]"));
}

#[test]
fn run_only_reserves_exact_help_options() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["run", "--help.spl"]);

    cmd.assert()
        .failure()
        .stdout(is_empty())
        .stderr(contains("Cannot read \"--help.spl\""));
}

#[test]
fn run_does_not_consume_help_after_a_source_filename() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["run", "missing-run-help-source.spl", "--help"]);

    cmd.assert()
        .failure()
        .stderr(contains("Cannot read \"missing-run-help-source.spl\"")
            .and(contains("Usage: simple run").not()));
}

#[test]
fn run_does_not_reserve_a_path_named_help() {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.args(["run", "./--help"]);

    cmd.assert()
        .failure()
        .stderr(contains("Cannot read").and(contains("Usage: simple run").not()));
}
