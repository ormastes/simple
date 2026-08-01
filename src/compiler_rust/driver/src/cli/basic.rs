//! Basic CLI operations: running files, code, and watching for changes.

use crate::cli::examples_safety::{
    is_timeout_error, run_isolated_example_file, timeout_error_message, ExamplesWatchdogGuard,
};
use crate::runner::Runner;
use crate::watcher::watch;
use simple_common::target::Target;
use std::path::{Path, PathBuf};

/// Exit status returned by `simple run <spec>` when BDD examples executed and at
/// least one of them failed.
///
/// This is deliberately the same status `simple test` uses for a failing spec, so
/// the two entry points agree and ordinary `if ! simple run x` CI checks behave.
/// The failure *mode* is made distinguishable by the `spec failure:` diagnostic
/// emitted alongside it (see `bdd_failure_exit_code`), which names the failed and
/// total example counts — a generic error also exits 1 but never prints that line,
/// and an interpreter crash exits 101.
const SPEC_EXAMPLE_FAILURE_EXIT: i32 = 1;

/// Total non-skipped examples and how many of them failed.
///
/// Input is the interpreter's per-example record,
/// `(describe_path, test_name, passed, skipped)`, as returned by
/// `simple_compiler::interpreter::get_test_results()`.
///
/// This is the same source `simple test` trusts (`cli/test_runner/execution.rs`).
/// It is deliberately NOT the `BDD_COUNTS` pair behind the printed
/// "N examples, M failures" line: that pair is reset to `(0, 0)` at the end of
/// every top-level describe block, so by the time the run returns it is always
/// zero — reading it would have produced a fresh fail-open. `BDD_TEST_RESULTS`
/// accumulates across the whole file instead, so a failure in a later describe
/// block still counts.
fn bdd_example_counts(results: &[(String, String, bool, bool)]) -> (usize, usize) {
    let mut total = 0usize;
    let mut failed = 0usize;
    for (_describe, _name, passed, skipped) in results.iter() {
        if *skipped {
            continue;
        }
        total += 1;
        if !*passed {
            failed += 1;
        }
    }
    (total, failed)
}

/// Derive a process exit status from the in-process BDD example results.
///
/// `run_file*` previously returned only the interpreted module's own exit code. A
/// spec file has no explicit `main` and so returns 0, which meant
/// `simple run <spec>` exited 0 even when the printed report said
/// "N examples, M failures" — a verification fail-open: any evidence justified by
/// "exit 0" from `simple run` was unevidenced. The per-example results were already
/// recorded and already consumed by `simple test`; nothing consumed them on the
/// `run` path. This function is that missing consumer.
///
/// Fail-closed rules:
/// * No example ran (empty results) -> leave `module_exit_code` untouched.
///   Non-spec programs run through this same path and must keep their own status.
/// * Any example failed -> `SPEC_EXAMPLE_FAILURE_EXIT`, even if the module
///   returned 0.
/// * A non-zero `module_exit_code` is always preserved: a real error must not be
///   masked by, or downgraded to, a spec-failure status.
fn bdd_failure_exit_code(module_exit_code: i32, results: &[(String, String, bool, bool)]) -> i32 {
    if module_exit_code != 0 {
        return module_exit_code;
    }
    let (total, failed) = bdd_example_counts(results);
    if failed == 0 {
        return module_exit_code;
    }
    eprintln!(
        "spec failure: {} of {} example(s) failed (exit {})",
        failed, total, SPEC_EXAMPLE_FAILURE_EXIT
    );
    SPEC_EXAMPLE_FAILURE_EXIT
}

/// Create a runner with appropriate GC configuration
pub fn create_runner(gc_log: bool, gc_off: bool) -> Runner {
    if gc_off {
        Runner::new_no_gc()
    } else if gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

struct EnvVarGuard {
    key: &'static str,
    previous: Option<String>,
}

impl EnvVarGuard {
    fn set(key: &'static str, value: &str) -> Self {
        let previous = std::env::var(key).ok();
        std::env::set_var(key, value);
        Self { key, previous }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match &self.previous {
            Some(value) => std::env::set_var(self.key, value),
            None => std::env::remove_var(self.key),
        }
    }
}

/// Run a closure with strict runtime-family import errors when target policy requires it.
pub fn with_strict_runtime_family_imports<T>(enabled: bool, run: impl FnOnce() -> T) -> T {
    if enabled {
        let _guard = EnvVarGuard::set("SIMPLE_STRICT_RUNTIME_FAMILY", "1");
        run()
    } else {
        run()
    }
}

/// Run a closure with strict runtime-family imports for baremetal/SimpleOS targets.
pub fn with_strict_runtime_family_for_target<T>(target: Option<&Target>, run: impl FnOnce() -> T) -> T {
    with_strict_runtime_family_imports(target.is_some_and(|target| target.is_baremetal()), run)
}

/// Resolve a user-provided source path from common launch locations.
///
/// Windows release binaries are often launched from `bin/release` while callers
/// pass repo-relative paths such as `src/app/main.spl`. Check the current
/// directory first, then walk executable ancestors so installed and bootstrap
/// layouts can still run repo-local sources.
pub fn resolve_existing_input_path(path: &Path) -> Option<PathBuf> {
    if path.exists() {
        return Some(path.to_path_buf());
    }

    if path.is_absolute() {
        return None;
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            let mut ancestor = Some(exe_dir);
            let mut depth = 0;
            while let Some(dir) = ancestor {
                let candidate = dir.join(path);
                if candidate.exists() {
                    return Some(candidate);
                }
                ancestor = dir.parent();
                depth += 1;
                if depth >= 8 {
                    break;
                }
            }
        }
    }

    if let Ok(home) = std::env::var("SIMPLE_HOME") {
        let candidate = PathBuf::from(home).join(path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    None
}

/// Run a source file (.spl) or compiled binary (.smf)
pub fn run_file(path: &Path, gc_log: bool, gc_off: bool) -> i32 {
    run_file_with_args(path, gc_log, gc_off, vec![])
}

/// Run a source file (.spl) with command-line arguments
pub fn run_file_with_args(path: &Path, gc_log: bool, gc_off: bool, args: Vec<String>) -> i32 {
    if let Some(code) = run_isolated_example_file(path, gc_log, gc_off, &args) {
        return code;
    }

    let path = path.to_path_buf();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let watchdog = ExamplesWatchdogGuard::for_path(&path);
        let runner = create_runner(gc_log, gc_off);
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");
        let result = if matches!(extension, "spl" | "simple" | "sscript" | "shs" | "") {
            if runner.is_jit_mode() {
                runner.run_file_with_args(&path, args)
            } else {
                runner.run_file_interpreted_with_args(&path, args)
            }
        } else {
            runner.run_file(&path)
        };
        match result {
            // Fail-closed: a spec whose examples failed must not exit 0 just
            // because the module body itself returned 0. See
            // `bdd_failure_exit_code`.
            Ok(code) => bdd_failure_exit_code(code, &simple_compiler::interpreter::get_test_results()),
            Err(e) => {
                if watchdog.is_active() && is_timeout_error(&e) {
                    eprintln!("error: {}", timeout_error_message(&path, watchdog.timeout_secs()));
                } else {
                    print_cli_error(&e);
                }
                1
            }
        }
    }));
    match result {
        Ok(code) => code,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: interpreter crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            101
        }
    }
}

/// Run code from a string
pub fn run_code(code: &str, gc_log: bool, gc_off: bool) -> i32 {
    let code = code.to_string();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let runner = create_runner(gc_log, gc_off);
        let print_exit_code = should_print_code_result(&code);

        // Wrap expression in main if not already a full program
        let full_code = if code.contains("main")
            || code.contains("fn ")
            || code.contains("let ")
            || code.contains("val ")
            || code.contains("var ")
        {
            code
        } else {
            format!("main = {}", code)
        };

        match runner.run_source_in_memory(&full_code) {
            Ok(exit_code) => {
                if print_exit_code {
                    println!("{}", exit_code);
                }
                exit_code
            }
            Err(e) => {
                print_cli_error(&e);
                1
            }
        }
    }));
    match result {
        Ok(code) => code,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: interpreter crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            101
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CliErrorDiagnostic {
    code: Option<&'static str>,
    message: String,
    help: Vec<&'static str>,
}

fn print_cli_error(error: &str) {
    let diagnostic = classify_cli_error(error);
    match diagnostic.code {
        Some(code) => eprintln!("error[{}]: {}", code, diagnostic.message),
        None => eprintln!("error: {}", diagnostic.message),
    }
    for help in diagnostic.help {
        eprintln!("  = help: {}", help);
    }
    // Function-not-found where every definition was an inactive @cfg(<arch>)
    // variant stripped for this host: explain WHY it is undefined (see
    // simple_compiler::pipeline::cfg_strip) instead of a bare not-found.
    if let Some(rest) = error.split("function `").nth(1) {
        if let Some(fn_name) = rest.split('`').next() {
            if let Some(hint) = simple_compiler::pipeline::cfg_strip::stripped_fn_hint(fn_name) {
                eprintln!("  = note: {}", hint);
            }
        }
    }
}

fn classify_cli_error(error: &str) -> CliErrorDiagnostic {
    if let Some(message) = error.strip_prefix("failed to read ") {
        return CliErrorDiagnostic {
            code: Some("E0001"),
            message: format!("cannot read file: {}", message),
            help: vec!["check that the path exists and is readable"],
        };
    }

    if let Some(message) = error.strip_prefix("parse error: ") {
        return CliErrorDiagnostic {
            code: Some("E0002"),
            message: message.to_string(),
            help: vec!["fix the syntax at the reported location"],
        };
    }

    if let Some(message) = error.strip_prefix("semantic: ") {
        if message.starts_with("function `") && message.ends_with("` not found") {
            return CliErrorDiagnostic {
                code: Some("E1002"),
                message: message.to_string(),
                help: vec!["check the function name or import the module that defines it"],
            };
        }
        if message == "division by zero" {
            return CliErrorDiagnostic {
                code: Some("E2001"),
                message: message.to_string(),
                help: vec!["check the divisor before dividing"],
            };
        }
    }

    CliErrorDiagnostic {
        code: None,
        message: error.to_string(),
        help: Vec::new(),
    }
}

fn should_print_code_result(code: &str) -> bool {
    let trimmed = code.trim();
    if trimmed.is_empty() || trimmed.contains('\n') {
        return false;
    }
    if trimmed.starts_with("main =") || trimmed.starts_with("main=") {
        return true;
    }
    if trimmed.starts_with("print ")
        || trimmed.starts_with("print(")
        || trimmed.starts_with("println ")
        || trimmed.starts_with("println(")
        || trimmed.starts_with("eprint ")
        || trimmed.starts_with("eprint(")
        || trimmed.starts_with("eprintln ")
        || trimmed.starts_with("eprintln(")
        || trimmed.starts_with("if ")
        || trimmed.starts_with("while ")
        || trimmed.starts_with("for ")
        || trimmed.starts_with("var ")
        || trimmed.starts_with("val ")
        || trimmed.starts_with("fn ")
        || trimmed.starts_with("class ")
        || trimmed.starts_with("struct ")
        || trimmed.starts_with("enum ")
        || trimmed.starts_with("use ")
        || trimmed.starts_with("extern ")
    {
        return false;
    }
    true
}

/// Watch a file for changes and auto-recompile
pub fn watch_file(path: &Path) -> i32 {
    println!("Watching {} for changes...", path.display());
    println!("Press Ctrl-C to stop.");

    match watch(path, true) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn classify_undefined_function_error() {
        let diagnostic = classify_cli_error("semantic: function `missing_function` not found");

        assert_eq!(diagnostic.code, Some("E1002"));
        assert_eq!(diagnostic.message, "function `missing_function` not found");
        assert!(!diagnostic.help.is_empty());
    }

    #[test]
    fn classify_division_by_zero_error() {
        let diagnostic = classify_cli_error("semantic: division by zero");

        assert_eq!(diagnostic.code, Some("E2001"));
        assert_eq!(diagnostic.message, "division by zero");
        assert!(!diagnostic.help.is_empty());
    }

    #[test]
    fn keeps_unclassified_error_message() {
        let diagnostic = classify_cli_error("codegen: backend unavailable");

        assert_eq!(diagnostic.code, None);
        assert_eq!(diagnostic.message, "codegen: backend unavailable");
        assert!(diagnostic.help.is_empty());
    }

    #[test]
    fn run_code_does_not_echo_exit_code_for_print_call_form() {
        // `-c 'print(1+1)'` must print only "2" — echoing the exit code
        // produced a stray "0" line (stage4 10th-site (c), 2026-06-11).
        assert!(!should_print_code_result("print(1+1)"));
        assert!(!should_print_code_result("println(\"x\")"));
        assert!(!should_print_code_result("eprint(\"x\")"));
        assert!(!should_print_code_result("eprintln(\"x\")"));
        assert!(!should_print_code_result("print \"x\""));
        // Bare expressions still echo their value.
        assert!(should_print_code_result("1+1"));
        assert!(should_print_code_result("main = 1+1"));
    }

    #[test]
    fn resolves_repo_relative_input_from_simple_home() {
        let root = std::env::temp_dir().join(format!("simple-driver-input-path-test-{}", std::process::id()));
        let source_dir = root.join("src").join("app");
        std::fs::create_dir_all(&source_dir).expect("create source dir");
        let source = source_dir.join("probe.spl");
        std::fs::write(&source, "print 1\n").expect("write source");

        let previous = std::env::var("SIMPLE_HOME").ok();
        std::env::set_var("SIMPLE_HOME", &root);
        let resolved = resolve_existing_input_path(&PathBuf::from("src/app/probe.spl"));
        match previous {
            Some(value) => std::env::set_var("SIMPLE_HOME", value),
            None => std::env::remove_var("SIMPLE_HOME"),
        }
        let _ = std::fs::remove_dir_all(&root);

        assert_eq!(resolved, Some(source));
    }

    #[test]
    fn strict_runtime_family_guard_restores_previous_env() {
        std::env::set_var("SIMPLE_STRICT_RUNTIME_FAMILY", "previous");
        let observed = with_strict_runtime_family_imports(true, || {
            std::env::var("SIMPLE_STRICT_RUNTIME_FAMILY").expect("strict env")
        });

        assert_eq!(observed, "1");
        assert_eq!(
            std::env::var("SIMPLE_STRICT_RUNTIME_FAMILY").expect("restored env"),
            "previous"
        );
        std::env::remove_var("SIMPLE_STRICT_RUNTIME_FAMILY");
    }

    #[test]
    fn strict_runtime_family_guard_leaves_env_unset_when_disabled() {
        std::env::remove_var("SIMPLE_STRICT_RUNTIME_FAMILY");
        let observed = with_strict_runtime_family_imports(false, || std::env::var("SIMPLE_STRICT_RUNTIME_FAMILY").ok());

        assert_eq!(observed, None);
        assert!(std::env::var("SIMPLE_STRICT_RUNTIME_FAMILY").is_err());
    }

    // --- exit status must track the BDD failure count -----------------------
    //
    // Fail-closed regression for the `simple run <spec>` exit-code fail-open:
    // the report said "N examples, M failures" while the process exited 0, so
    // any result in this repo justified by "exit 0" from `simple run` was
    // unevidenced. These pin the decision function; `interpreter_bdd.rs`
    // (`bdd_matcher_pass_after_failure_keeps_example_failed`,
    // `bdd_bare_falsy_call_without_matcher_still_fails`) pins it end-to-end.

    /// `(describe_path, test_name, passed, skipped)`, matching
    /// `simple_compiler::interpreter::get_test_results()`.
    fn ex(group: &str, name: &str, passed: bool, skipped: bool) -> (String, String, bool, bool) {
        (group.to_string(), name.to_string(), passed, skipped)
    }

    #[test]
    fn bdd_exit_code_is_non_zero_when_any_example_failed() {
        // The exact shape that exited 0 before the fix.
        let results = vec![ex("control", "fails", false, false)];
        assert_eq!(bdd_failure_exit_code(0, &results), SPEC_EXAMPLE_FAILURE_EXIT);
        assert_ne!(bdd_failure_exit_code(0, &results), 0);
    }

    #[test]
    fn bdd_exit_code_tracks_failures_across_multiple_describe_blocks() {
        // Aggregation must not stop at the first block: a later failing block is
        // exactly the "silently dropped" shape the sibling multi-path bug had.
        // This also pins the choice of BDD_TEST_RESULTS over BDD_COUNTS, which is
        // zeroed at the end of every top-level describe.
        let late_failure = vec![
            ex("first", "ok", true, false),
            ex("first", "ok too", true, false),
            ex("second", "fails", false, false),
        ];
        let early_failure = vec![ex("first", "fails", false, false), ex("second", "ok", true, false)];
        let all_clean = vec![ex("first", "ok", true, false), ex("second", "ok", true, false)];
        assert_eq!(bdd_failure_exit_code(0, &late_failure), SPEC_EXAMPLE_FAILURE_EXIT);
        assert_eq!(bdd_failure_exit_code(0, &early_failure), SPEC_EXAMPLE_FAILURE_EXIT);
        assert_eq!(bdd_failure_exit_code(0, &all_clean), 0);
    }

    #[test]
    fn bdd_exit_code_stays_zero_for_clean_specs() {
        let results = vec![ex("control", "passes", true, false)];
        assert_eq!(bdd_failure_exit_code(0, &results), 0);
    }

    #[test]
    fn bdd_exit_code_ignores_programs_with_no_examples() {
        // Non-spec programs share this run path and must keep their own status.
        assert_eq!(bdd_failure_exit_code(0, &[]), 0);
        assert_eq!(bdd_failure_exit_code(7, &[]), 7);
    }

    #[test]
    fn bdd_exit_code_treats_skipped_examples_as_neither_pass_nor_fail() {
        // A skipped example carries passed=false; counting it as a failure would
        // turn every ignored test into a red run.
        let results = vec![ex("control", "ignored", false, true)];
        assert_eq!(bdd_failure_exit_code(0, &results), 0);
        assert_eq!(bdd_example_counts(&results), (0, 0));
    }

    #[test]
    fn bdd_exit_code_never_masks_a_real_error_status() {
        // A genuine non-zero must survive, not be rewritten to the spec status,
        // so "examples failed" stays distinguishable from other failure modes.
        assert_eq!(bdd_failure_exit_code(101, &[ex("g", "n", false, false)]), 101);
        assert_eq!(bdd_failure_exit_code(2, &[ex("g", "n", true, false)]), 2);
    }
}
