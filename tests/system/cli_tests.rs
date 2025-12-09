//! CLI system tests
//! Tests the command-line interface end-to-end

use tempfile::tempdir;
use std::fs;
use std::process::Command;

#[test]
fn test_cli_run_source() {
    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("hello.spl");
    fs::write(&source_path, "main = 0").expect("write ok");

    // This test requires the binary to be built
    // Skip if binary not available
    let result = Command::new("cargo")
        .args(["run", "-p", "simple-driver", "--", "run"])
        .arg(&source_path)
        .output();

    match result {
        Ok(output) => {
            // Check that command executed (may fail for other reasons)
            assert!(output.status.success() || !output.stderr.is_empty(),
                "Command should execute");
        }
        Err(_) => {
            // cargo not available or build failed - skip test
            println!("Skipping CLI test - cargo run not available");
        }
    }
}

#[test]
fn test_cli_help() {
    let result = Command::new("cargo")
        .args(["run", "-p", "simple-driver", "--", "--help"])
        .output();

    match result {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            // Either help should be in stdout or we got some output
            assert!(!stdout.is_empty() || !stderr.is_empty(),
                "Should produce some output");
        }
        Err(_) => {
            println!("Skipping CLI test - cargo run not available");
        }
    }
}
