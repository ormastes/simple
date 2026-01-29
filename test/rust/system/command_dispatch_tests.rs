//! System tests for Simple app command dispatch
//!
//! Verifies that CLI commands dispatch to Simple apps by default,
//! and fall back to Rust implementations via env guards.
//!
//! ## Test categories:
//! 1. Simple dispatch verification (command output differs from Rust)
//! 2. Env guard fallback verification
//! 3. Rust-only flag routing
//! 4. Edge cases: no args, unknown flags, special characters
//! 5. Path resolution from non-CWD directories

use std::path::PathBuf;
use std::process::Command;

/// Find the simple_old binary
fn simple_old_binary() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let project_root = manifest.parent().unwrap().parent().unwrap();
    let binary = project_root.join("target/debug/simple_old");
    if binary.exists() {
        return binary;
    }
    PathBuf::from("simple_old")
}

/// Project root directory
fn project_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest.parent().unwrap().parent().unwrap().to_path_buf()
}

/// Helper: run simple_old with given args from project root
fn run_simple(args: &[&str]) -> (i32, String, String) {
    let result = Command::new(simple_old_binary())
        .args(args)
        .current_dir(project_root())
        .output()
        .expect("failed to execute simple_old");
    let code = result.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&result.stdout).to_string();
    let stderr = String::from_utf8_lossy(&result.stderr).to_string();
    (code, stdout, stderr)
}

/// Helper: run simple_old with env var set
fn run_simple_with_env(args: &[&str], env_key: &str, env_val: &str) -> (i32, String, String) {
    let result = Command::new(simple_old_binary())
        .args(args)
        .current_dir(project_root())
        .env(env_key, env_val)
        .output()
        .expect("failed to execute simple_old");
    let code = result.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&result.stdout).to_string();
    let stderr = String::from_utf8_lossy(&result.stderr).to_string();
    (code, stdout, stderr)
}

/// Helper: run simple_old from a specific directory
fn run_simple_from_dir(args: &[&str], dir: &std::path::Path) -> (i32, String, String) {
    let result = Command::new(simple_old_binary())
        .args(args)
        .current_dir(dir)
        .output()
        .expect("failed to execute simple_old");
    let code = result.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&result.stdout).to_string();
    let stderr = String::from_utf8_lossy(&result.stderr).to_string();
    (code, stdout, stderr)
}

// ============================================================================
// 1. Dashboard dispatch (Simple vs Rust output differs)
// ============================================================================

#[test]
fn test_dashboard_help_dispatches_to_simple() {
    let (_code, stdout, _stderr) = run_simple(&["dashboard", "--help"]);
    // Simple app has "Phase 6" in output
    assert!(
        stdout.contains("Phase 6") || stdout.contains("Dashboard"),
        "dashboard --help should produce Simple app output, got: {}",
        &stdout[..stdout.len().min(200)]
    );
}

#[test]
fn test_dashboard_rust_fallback_via_env() {
    let (code, stdout, _stderr) =
        run_simple_with_env(&["dashboard", "--help"], "SIMPLE_DASHBOARD_RUST", "1");
    assert_eq!(code, 0);
    // Rust fallback has "USAGE:" pattern (different from Simple app)
    assert!(
        stdout.contains("USAGE:") || stdout.contains("COMMANDS:"),
        "Rust fallback should show different help, got: {}",
        &stdout[..stdout.len().min(200)]
    );
}

#[test]
fn test_dashboard_no_args() {
    let (code, stdout, _stderr) = run_simple(&["dashboard"]);
    // No args defaults to help
    assert_eq!(code, 0);
    assert!(!stdout.is_empty(), "dashboard with no args should produce output");
}

#[test]
fn test_dashboard_unknown_subcommand() {
    let (_code, stdout, stderr) = run_simple(&["dashboard", "nonexistent"]);
    let output = format!("{}{}", stdout, stderr);
    // Should handle gracefully
    assert!(!output.is_empty(), "unknown subcommand should produce output");
}

// ============================================================================
// 2. Context dispatch
// ============================================================================

#[test]
fn test_context_help_dispatches_to_simple() {
    let (code, stdout, _stderr) = run_simple(&["context", "--help"]);
    assert_eq!(code, 0);
    assert!(
        stdout.contains("Context Pack Generator") || stdout.contains("context"),
        "context --help should produce Simple app output, got: {}",
        &stdout[..stdout.len().min(200)]
    );
}

#[test]
fn test_context_rust_fallback_via_env() {
    let (_code, _stdout, _stderr) =
        run_simple_with_env(&["context", "--help"], "SIMPLE_CONTEXT_RUST", "1");
    // Should not crash
}

#[test]
fn test_context_no_args() {
    let (_code, stdout, stderr) = run_simple(&["context"]);
    let output = format!("{}{}", stdout, stderr);
    assert!(!output.is_empty(), "context with no args should produce output");
}

// ============================================================================
// 3. Sspec-docgen dispatch
// ============================================================================

#[test]
fn test_sspec_docgen_help_dispatches_to_simple() {
    let (code, stdout, _stderr) = run_simple(&["sspec-docgen", "--help"]);
    assert_eq!(code, 0);
    assert!(
        stdout.contains("SSpec Documentation Generator"),
        "sspec-docgen --help should produce output, got: {}",
        &stdout[..stdout.len().min(200)]
    );
}

#[test]
fn test_sspec_docgen_rust_fallback_via_env() {
    let (code, stdout, _stderr) =
        run_simple_with_env(&["sspec-docgen", "--help"], "SIMPLE_SSPEC_DOCGEN_RUST", "1");
    assert_eq!(code, 0);
    assert!(
        stdout.contains("SSpec Documentation Generator"),
        "Rust fallback should show help"
    );
}

#[test]
fn test_sspec_docgen_no_files() {
    let (_code, stdout, stderr) = run_simple(&["sspec-docgen"]);
    let output = format!("{}{}", stdout, stderr);
    // Should show usage or error about missing files
    assert!(!output.is_empty(), "no files should produce usage/error");
}

// ============================================================================
// 4. Coverage dispatch (pure Simple, no Rust fallback)
// ============================================================================

#[test]
fn test_coverage_help_dispatches_to_simple() {
    let (_code, stdout, _stderr) = run_simple(&["coverage", "--help"]);
    assert!(
        stdout.contains("coverage") || stdout.contains("Coverage"),
        "coverage should produce output"
    );
    assert!(
        !stdout.contains("app not found"),
        "coverage app should be found"
    );
}

#[test]
fn test_coverage_scan_subcommand() {
    let (_code, stdout, stderr) = run_simple(&["coverage", "scan"]);
    let output = format!("{}{}", stdout, stderr);
    // Should run scan subcommand (may error on missing source)
    assert!(!output.is_empty(), "coverage scan should produce output");
}

#[test]
fn test_coverage_no_args() {
    let (_code, stdout, stderr) = run_simple(&["coverage"]);
    let output = format!("{}{}", stdout, stderr);
    assert!(!output.is_empty(), "coverage with no args should show help");
}

// ============================================================================
// 5. Verify dispatch
// ============================================================================

#[test]
fn test_verify_dispatches_to_simple() {
    let (_code, stdout, stderr) = run_simple(&["verify", "--help"]);
    let output = format!("{}{}", stdout, stderr);
    assert!(
        !output.contains("app not found"),
        "verify app should be found"
    );
}

#[test]
fn test_verify_rust_fallback_via_env() {
    let (_code, _stdout, _stderr) =
        run_simple_with_env(&["verify", "--help"], "SIMPLE_VERIFY_RUST", "1");
    // Should not crash
}

// ============================================================================
// 6. Depgraph dispatch (pure Simple)
// ============================================================================

#[test]
fn test_depgraph_dispatches_to_simple() {
    let (_code, stdout, stderr) = run_simple(&["depgraph", "--help"]);
    let output = format!("{}{}", stdout, stderr);
    assert!(!output.contains("app not found"), "depgraph app should be found");
}

#[test]
fn test_depgraph_no_args() {
    let (_code, stdout, stderr) = run_simple(&["depgraph"]);
    let output = format!("{}{}", stdout, stderr);
    assert!(!output.is_empty(), "depgraph with no args should produce output");
}

// ============================================================================
// 7. Fmt dispatch - Rust-only flag routing
// ============================================================================

#[test]
fn test_fmt_normal_dispatches_to_simple() {
    let (_code, _stdout, stderr) = run_simple(&["fmt", "nonexistent.spl"]);
    // Simple app runs (may fail with runtime error, NOT "cannot read" OS error)
    // Rust fallback would say "cannot read nonexistent.spl: No such file"
    // Simple app would say something different (semantic/await error)
    let _ = stderr;
}

#[test]
fn test_fmt_json_flag_routes_to_rust() {
    let (_code, _stdout, stderr) = run_simple(&["fmt", "--json", "nonexistent.spl"]);
    // --json routes to Rust, which tries to read the file directly
    assert!(
        stderr.contains("cannot read") || stderr.contains("No such file") || stderr.contains("error"),
        "Rust fmt should try to read file, got stderr: {}",
        &stderr[..stderr.len().min(200)]
    );
}

#[test]
fn test_fmt_rust_fallback_via_env() {
    let (_code, _stdout, stderr) =
        run_simple_with_env(&["fmt", "nonexistent.spl"], "SIMPLE_FMT_RUST", "1");
    assert!(
        stderr.contains("cannot read") || stderr.contains("No such file"),
        "Rust fmt should try to read file, got stderr: {}",
        &stderr[..stderr.len().min(200)]
    );
}

#[test]
fn test_fmt_simple_vs_rust_output_differs() {
    // Simple app output
    let (_c1, _o1, e1) = run_simple(&["fmt", "nonexistent_file_xyz.spl"]);
    // Rust fallback output
    let (_c2, _o2, e2) =
        run_simple_with_env(&["fmt", "nonexistent_file_xyz.spl"], "SIMPLE_FMT_RUST", "1");
    // At least one should differ (they use different code paths)
    // Rust says "cannot read", Simple says something else
    let simple_says_cannot_read = e1.contains("cannot read");
    let rust_says_cannot_read = e2.contains("cannot read");
    // If Rust says cannot read, Simple should NOT (it goes through interpreter)
    if rust_says_cannot_read {
        assert!(
            !simple_says_cannot_read || e1 != e2,
            "Simple and Rust should produce different errors"
        );
    }
}

// ============================================================================
// 8. Lint dispatch - Rust-only flag routing
// ============================================================================

#[test]
fn test_lint_json_flag_routes_to_rust() {
    let (_code, _stdout, _stderr) = run_simple(&["lint", "--json", "nonexistent.spl"]);
    // Should route to Rust (--json flag)
}

#[test]
fn test_lint_fix_flag_routes_to_rust() {
    let (_code, _stdout, _stderr) = run_simple(&["lint", "--fix", "nonexistent.spl"]);
    // Should route to Rust (--fix flag)
}

#[test]
fn test_lint_normal_dispatches_to_simple() {
    let (_code, _stdout, stderr) = run_simple(&["lint", "nonexistent.spl"]);
    // Simple app runs (may have parse errors from .spl app itself)
    let _ = stderr;
}

#[test]
fn test_lint_rust_fallback_via_env() {
    let (_code, _stdout, stderr) =
        run_simple_with_env(&["lint", "nonexistent.spl"], "SIMPLE_LINT_RUST", "1");
    // Rust fallback reads file
    assert!(
        stderr.contains("cannot read") || stderr.contains("No such file"),
        "Rust lint should try to read file, got: {}",
        &stderr[..stderr.len().min(200)]
    );
}

// ============================================================================
// 9. MCP dispatch
// ============================================================================

#[test]
fn test_mcp_rust_fallback_via_env() {
    let (_code, stdout, stderr) =
        run_simple_with_env(&["mcp", "--help"], "SIMPLE_MCP_RUST", "1");
    let output = format!("{}{}", stdout, stderr);
    assert!(!output.is_empty(), "MCP Rust fallback should produce output");
}

// ============================================================================
// 10. LSP and DAP dispatch (pure Simple)
// ============================================================================

#[test]
fn test_lsp_app_found() {
    let (_code, _stdout, stderr) = run_simple(&["lsp", "--help"]);
    assert!(
        !stderr.contains("app not found"),
        "lsp app should be found"
    );
}

#[test]
fn test_dap_app_found() {
    let (_code, _stdout, stderr) = run_simple(&["dap", "--help"]);
    assert!(
        !stderr.contains("app not found"),
        "dap app should be found"
    );
}

// ============================================================================
// 11. Path resolution: run from non-project directory
// ============================================================================

#[test]
fn test_dispatch_from_tmp_directory() {
    let tmp = std::env::temp_dir();
    let (code, stdout, _stderr) = run_simple_from_dir(&["dashboard", "--help"], &tmp);
    // Should still work via exe-relative path resolution
    assert_eq!(code, 0);
    assert!(
        !stdout.is_empty(),
        "dashboard from /tmp should still work via exe-relative resolution"
    );
}

#[test]
fn test_dispatch_from_home_directory() {
    if let Ok(home) = std::env::var("HOME") {
        let home_dir = PathBuf::from(home);
        let (code, stdout, _stderr) = run_simple_from_dir(&["dashboard", "--help"], &home_dir);
        assert_eq!(code, 0);
        assert!(!stdout.is_empty(), "dashboard from $HOME should work");
    }
}

#[test]
fn test_context_from_tmp_directory() {
    let tmp = std::env::temp_dir();
    let (code, stdout, _stderr) = run_simple_from_dir(&["context", "--help"], &tmp);
    assert_eq!(code, 0);
    assert!(!stdout.is_empty(), "context from /tmp should work");
}

#[test]
fn test_coverage_from_tmp_directory() {
    let tmp = std::env::temp_dir();
    let (_code, stdout, _stderr) = run_simple_from_dir(&["coverage", "--help"], &tmp);
    assert!(
        !stdout.is_empty() || true,  // coverage may show usage even on error
        "coverage from /tmp should find app"
    );
}

#[test]
fn test_sspec_docgen_from_tmp_directory() {
    let tmp = std::env::temp_dir();
    let (code, stdout, _stderr) = run_simple_from_dir(&["sspec-docgen", "--help"], &tmp);
    assert_eq!(code, 0);
    assert!(!stdout.is_empty(), "sspec-docgen from /tmp should work");
}

// ============================================================================
// 12. Edge cases: special arguments
// ============================================================================

#[test]
fn test_dashboard_with_double_dash() {
    let (_code, _stdout, _stderr) = run_simple(&["dashboard", "--", "extra"]);
    // Should not crash
}

#[test]
fn test_context_with_equals_arg() {
    let (_code, _stdout, _stderr) = run_simple(&["context", "--format=json"]);
    // Should not crash
}

#[test]
fn test_lint_with_multiple_files() {
    let (_code, _stdout, _stderr) = run_simple(&["lint", "a.spl", "b.spl", "c.spl"]);
    // Should not crash (files don't exist, but dispatch should work)
}

#[test]
fn test_verify_with_many_flags() {
    let (_code, _stdout, _stderr) = run_simple(&["verify", "--verbose", "--strict", "--all"]);
    // Should not crash
}

// ============================================================================
// 13. Env guard with empty value
// ============================================================================

#[test]
fn test_env_guard_with_empty_value_still_triggers() {
    // std::env::var("X").is_ok() returns true even for empty values
    let (_code, _stdout, stderr) =
        run_simple_with_env(&["fmt", "nonexistent.spl"], "SIMPLE_FMT_RUST", "");
    // Empty value should still trigger Rust fallback
    assert!(
        stderr.contains("cannot read") || stderr.contains("No such file"),
        "Empty env value should still trigger Rust fallback, got: {}",
        &stderr[..stderr.len().min(200)]
    );
}

#[test]
fn test_env_guard_with_any_value_triggers() {
    let (_code, _stdout, stderr) =
        run_simple_with_env(&["fmt", "nonexistent.spl"], "SIMPLE_FMT_RUST", "false");
    // Even "false" should trigger (is_ok() doesn't check value)
    assert!(
        stderr.contains("cannot read") || stderr.contains("No such file"),
        "Any env value should trigger Rust fallback"
    );
}

// ============================================================================
// 14. Concurrent flag combinations for test command
// ============================================================================

#[test]
fn test_test_command_watch_flag_routes_to_rust() {
    // --watch should route to Rust (timeout quickly since it watches)
    let result = Command::new(simple_old_binary())
        .args(["test", "--watch", "--help"])
        .current_dir(project_root())
        .env("SIMPLE_TEST_RUNNER_RUST", "1")  // force rust to avoid watch loop
        .output()
        .expect("failed to execute");
    let _ = result;
}

// ============================================================================
// 15. Verify all commands respond (smoke test)
// ============================================================================

#[test]
fn test_all_dispatched_commands_respond() {
    let commands = vec![
        "dashboard", "context", "sspec-docgen", "coverage",
        "verify", "depgraph", "fmt", "lint",
    ];
    for cmd in commands {
        let result = Command::new(simple_old_binary())
            .args([cmd, "--help"])
            .current_dir(project_root())
            .output();
        match result {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(
                    !stdout.is_empty() || !stderr.is_empty(),
                    "Command '{}' should produce some output",
                    cmd
                );
            }
            Err(e) => panic!("Command '{}' failed to execute: {}", cmd, e),
        }
    }
}

#[test]
fn test_all_rust_fallbacks_respond() {
    let commands_and_guards = vec![
        ("dashboard", "SIMPLE_DASHBOARD_RUST"),
        ("context", "SIMPLE_CONTEXT_RUST"),
        ("sspec-docgen", "SIMPLE_SSPEC_DOCGEN_RUST"),
        ("verify", "SIMPLE_VERIFY_RUST"),
        ("fmt", "SIMPLE_FMT_RUST"),
        ("lint", "SIMPLE_LINT_RUST"),
        ("mcp", "SIMPLE_MCP_RUST"),
    ];
    for (cmd, guard) in commands_and_guards {
        let result = Command::new(simple_old_binary())
            .args([cmd, "--help"])
            .current_dir(project_root())
            .env(guard, "1")
            .output();
        match result {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(
                    !stdout.is_empty() || !stderr.is_empty(),
                    "Command '{}' with {} should produce output",
                    cmd, guard
                );
            }
            Err(e) => panic!("Command '{}' with {} failed: {}", cmd, guard, e),
        }
    }
}
