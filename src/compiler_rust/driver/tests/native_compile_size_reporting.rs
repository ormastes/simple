#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use assert_cmd::Command;
use std::fs;
use std::path::{Path, PathBuf};
use tempfile::tempdir;

fn project_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().unwrap().parent().unwrap().to_path_buf()
}

fn write_minimal_program(dir: &Path) -> PathBuf {
    let source = dir.join("size_probe.spl");
    fs::write(&source, "fn main() -> i32:\n    return 0\n").expect("write source");
    source
}

fn parse_reported_size(stdout: &str) -> u64 {
    let marker = " -> ";
    let bytes_marker = " bytes,";
    let start = stdout
        .find(marker)
        .and_then(|idx| stdout[idx..].find('(').map(|open| idx + open + 1))
        .expect("reported size prefix");
    let end = stdout[start..]
        .find(bytes_marker)
        .map(|idx| start + idx)
        .expect("reported size suffix");
    stdout[start..end].trim().parse::<u64>().expect("numeric size")
}

fn run_native_compile(extra_args: &[&str]) -> (String, PathBuf) {
    let dir = tempdir().expect("tempdir");
    let dir_path = dir.keep();
    let source = write_minimal_program(&dir_path);
    let output = dir_path.join("native_size_probe");

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("simple"));
    cmd.current_dir(project_root())
        .arg("compile")
        .arg(&source)
        .arg("--native")
        .arg("-o")
        .arg(&output);
    for arg in extra_args {
        cmd.arg(arg);
    }

    let assert = cmd.assert().success();
    let stdout = String::from_utf8(assert.get_output().stdout.clone()).expect("utf8 stdout");
    (stdout, output)
}

#[test]
fn native_compile_reports_final_size_after_default_debug_strip() {
    let (stdout, output) = run_native_compile(&[]);
    let reported = parse_reported_size(&stdout);
    let actual = fs::metadata(&output).expect("output metadata").len();
    assert_eq!(reported, actual, "stdout should report final on-disk size");
}

#[test]
fn native_compile_reports_final_size_when_no_strip_is_requested() {
    let (stdout, output) = run_native_compile(&["--no-strip"]);
    let reported = parse_reported_size(&stdout);
    let actual = fs::metadata(&output).expect("output metadata").len();
    assert_eq!(reported, actual, "stdout should report final on-disk size");
}
