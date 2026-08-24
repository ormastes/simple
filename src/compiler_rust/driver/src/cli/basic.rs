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

/// Exit status returned by `simple run <spec>` when the file executed FEWER
/// examples than it unconditionally declares — i.e. examples were silently
/// dropped.
///
/// Same status as a spec-example failure, because it is one: a dropped example
/// is an example that did not pass. The mode is distinguishable by the
/// `DROPPED:` diagnostic, which no other failure prints.
const SPEC_EXAMPLE_DROPPED_EXIT: i32 = 1;

/// Exit status for a spec run that TIMED OUT.
///
/// Deliberately NOT `1`: `1` is the spec-example-failure status, and a timeout is
/// UNVERIFIED, never a failure. `124` is the conventional timeout status (GNU
/// `timeout(1)`), so an outer classifier that knows nothing about this file still
/// reads it as "killed on time", not "the examples failed".
const SPEC_TIMEOUT_EXIT: i32 = 124;

/// The classified terminal outcome of running one spec file, as seen from INSIDE
/// the process that ran it.
///
/// These are the same classes the `Results:` summary uses. Two notes on the ones
/// that are absent here rather than unhandled:
///
/// * `TERMINATED` cannot be produced in-process. It means the process died on a
///   signal (earlyoom's SIGTERM -> 143), so no code in this process runs
///   afterwards to report it; the parent classifies it from the wait status. The
///   variant exists so the mapping is total and so callers cannot silently
///   collapse it into `Crashed`. Per the contract an unbudgeted SIGKILL(137) is
///   `Crashed`, not `Terminated`.
/// * `NotRun` is likewise assigned by the parent for a file it never launched.
///
/// `Timeout`, `Terminated` and `NotRun` are UNVERIFIED: they carry no verdict
/// about the examples, and must never be counted as failures.
// `Terminated` and `NotRun` are assigned by the PARENT process, never constructed
// here; they exist so the class set is complete and cannot silently collapse into
// a neighbouring class.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SpecOutcome {
    /// The module ran to completion. Its examples are a verdict.
    Ok,
    /// The run returned an error (compile/runtime error surfaced as `Err`).
    Error,
    /// The interpreter panicked, or the process died by an unbudgeted signal.
    Crashed,
    /// Killed on a signal by an external supervisor (SIGTERM/143). UNVERIFIED.
    Terminated,
    /// Killed by the examples watchdog. UNVERIFIED.
    Timeout,
    /// Never launched. UNVERIFIED.
    NotRun,
}

impl SpecOutcome {
    /// The token printed as `outcome=` on the verdict line.
    fn as_str(self) -> &'static str {
        match self {
            SpecOutcome::Ok => "OK",
            SpecOutcome::Error => "ERROR",
            SpecOutcome::Crashed => "CRASHED",
            SpecOutcome::Terminated => "TERMINATED",
            SpecOutcome::Timeout => "TIMEOUT",
            SpecOutcome::NotRun => "NOT_RUN",
        }
    }

    /// Whether the run produced a verdict about the examples at all.
    ///
    /// `false` for the UNVERIFIED classes, whose partial tallies must not be
    /// counted as failures or drops.
    fn is_verified(self) -> bool {
        matches!(self, SpecOutcome::Ok | SpecOutcome::Error | SpecOutcome::Crashed)
    }

    /// Whether `executed < declared` is meaningful as a *silent drop* for this
    /// outcome. Only a normally-completed run qualifies: every other class has an
    /// independent reason for having executed fewer examples.
    fn drop_check_applies(self) -> bool {
        matches!(self, SpecOutcome::Ok)
    }

    /// The process status for this outcome, given the status the run itself
    /// produced. Single source of truth, so the printed line and the exit code
    /// are derived from the same value.
    fn exit_code(self, module_exit_code: i32) -> i32 {
        match self {
            SpecOutcome::Timeout => SPEC_TIMEOUT_EXIT,
            _ => module_exit_code,
        }
    }
}

/// Number of examples the run actually executed, including skipped ones.
///
/// Skipped examples are still *executed* as far as registration goes — they are
/// recorded in `BDD_TEST_RESULTS` — so they must be counted here, otherwise a
/// legitimately-skipped example would be reported as dropped.
fn bdd_executed_count(results: &[(String, String, bool, bool)]) -> usize {
    results.len()
}

/// Detect silently dropped examples and emit the authoritative per-file verdict.
///
/// # The defect this closes
///
/// When a statement in a `describe` body aborts at registration time — a bare
/// `return`, a symbol that only resolves inside that block, an import that
/// failed — the remaining `it` blocks in that group and every LATER top-level
/// `describe` are never registered. The run prints a green per-describe summary
/// (`0 examples, 0 failures`) for the truncated group, omits the vanished groups
/// entirely, and exits 0. Measured on a five-example fixture whose second
/// `describe` body begins with a bare `return`: 3 of 5 examples executed,
/// all-green output, exit 0, and no line anywhere saying two examples were lost.
///
/// # The reporting defect this also closes
///
/// The `N examples, M failures` line is printed once per top-level `describe`,
/// and the file-level `spec failure:` line is printed only on failure and only
/// to stderr. So `tail -1` of a spec log yields the LAST GROUP's count, not the
/// file's. Measured: the nine-example `trait_scanner_spec.spl` ends its stdout
/// with `3 examples, 0 failures` — the size of its last `describe`. This is
/// exactly the "9 examples became 3" report; the file's real verdict was never
/// printed at all.
///
/// The fix is a single authoritative line per FILE, always, on stdout, last:
///
/// ```text
/// SPEC FILE VERDICT: <path> declared>=9 executed=9 passed=9 failed=0 dropped=0
/// ```
///
/// It deliberately does NOT contain the substring `examples, ` or `failures`:
/// `src/app/test_runner_new/test_runner_single.spl` SUMS every per-describe
/// `N examples, M failures` line it sees, so a file-level line in that shape
/// would double every count in the repo. The existing per-describe lines and the
/// `Results: N total, M passed, K failed` contract are untouched.
///
/// # Why this cannot cry wolf
///
/// `declared` is `unconditional_example_floor` — a strict lower bound counting
/// only examples reachable through module-level statements and describe/context
/// bodies. Conditional generation (`if cfg:`, `for x in xs:`), runtime expansion
/// (`it_behaves_like`), and skip/pending forms all contribute ZERO to the floor,
/// so a file that legitimately runs fewer, more, or a variable number of
/// examples than another can never trip the check. Only `executed < floor` —
/// which is arithmetically impossible without a drop — is reported.
///
/// # The contradiction this closes (2026-08-18)
///
/// The verdict line used to be emitted on ONE path only — the `Ok(code)` arm of
/// `run_file_common` — while the run has three terminal shapes: normal return,
/// `Err` (which includes the examples-watchdog TIMEOUT), and a caught panic
/// (CRASHED). On a timeout the run printed `error: ... timed out ...` to stderr
/// and exited **1**, the exact status of a spec-example failure, with **no**
/// verdict line at all. Anything classifying by exit status therefore booked an
/// UNVERIFIED timeout as a failure, contradicting the `Results:` contract in
/// which TIMEOUT and TERMINATED are never failures — and `tail -1` of the log,
/// which the line above promises is authoritative for the FILE, silently
/// returned the last `describe`'s count instead. A caught panic had the same
/// hole at status 101.
///
/// Two smaller divergences in the line itself:
/// * `skipped` was computed and never printed, so `passed + failed` did not add
///   up to `executed` for any file with a skipped example, and a reader
///   reconciling the two numbers saw a phantom drop.
/// * `dropped` was derived unconditionally, so an UNVERIFIED run — which by
///   definition executed fewer examples than it declared — would have been
///   reported as a silent drop, i.e. as a failure.
///
/// The fix is that every terminal shape routes through this one function with an
/// explicit `SpecOutcome`, the line always carries `outcome=` and `skipped=`, and
/// both the drop verdict and the failure counts are suppressed for the UNVERIFIED
/// classes. The exit status is derived from the same outcome, so the line and the
/// status cannot disagree.
fn report_spec_file_verdict(
    path: &Path,
    outcome: SpecOutcome,
    module_exit_code: i32,
    results: &[(String, String, bool, bool)],
) -> i32 {
    let declared = match declared_example_floor(path) {
        Some(n) => n,
        // Unparseable or unreadable: the run itself would have failed. Never
        // invent a drop from a measurement we could not take.
        None => return module_exit_code,
    };
    let executed = bdd_executed_count(results);

    // Not a spec file at all: no examples declared and none ran. Ordinary
    // programs must keep their own status and print nothing extra.
    if declared == 0 && executed == 0 {
        return module_exit_code;
    }

    let (counted_total, failed) = bdd_example_counts(results);
    let passed = counted_total.saturating_sub(failed);
    let skipped = executed.saturating_sub(counted_total);
    // An UNVERIFIED run executed fewer examples than it declared BY DEFINITION —
    // it was killed. That is not a silent drop and must never be reported as one.
    // A CRASHED run also executes fewer examples than it declared, but the cause
    // is the crash, not a registration drop; only a run that completed normally
    // can be measured for silent drops.
    let dropped = if outcome.drop_check_applies() {
        declared.saturating_sub(executed)
    } else {
        0
    };
    // Likewise its partial per-example tally is not a verdict: a spec killed
    // mid-example must not contribute failures to any accounting.
    let failed = if outcome.is_verified() { failed } else { 0 };

    // INVARIANT, enforced in exactly one place: `failed > 0` implies a non-OK
    // outcome, which implies a non-zero exit status.
    //
    // `SpecOutcome::Ok` means only "the module ran to completion" — it is
    // decided before the BDD table is tallied — so a run whose examples failed
    // printed `outcome=OK ... failed=1`, and when the module itself returned a
    // clean status the process also exited 0. The failure was computed
    // correctly and then discarded on the way out. Same fail-open family as
    // SdnTable::update_row's dropped bool. See doc/08_tracking/bug/
    // test_runner_exits_zero_on_failed_spec_2026-08-21.md
    let outcome = if failed > 0 && outcome == SpecOutcome::Ok {
        SpecOutcome::Error
    } else {
        outcome
    };
    let module_exit_code = if failed > 0 && module_exit_code == 0 {
        1
    } else {
        module_exit_code
    };

    println!(
        "SPEC FILE VERDICT: {} outcome={} declared>={} executed={} passed={} failed={} skipped={} dropped={}",
        path.display(),
        outcome.as_str(),
        declared,
        executed,
        passed,
        failed,
        skipped,
        dropped
    );

    if !outcome.is_verified() {
        // The status is derived from the outcome, not recomputed, so the line and
        // the exit code can never disagree about which class this run was in.
        return outcome.exit_code(module_exit_code);
    }

    if dropped > 0 {
        eprintln!(
            "DROPPED: {} of {} unconditionally-declared example(s) in {} never executed. \
             A describe/it block was skipped — typically a module-load or registration \
             failure inside a describe body. The examples that did run are NOT a verdict \
             for this file.",
            dropped,
            declared,
            path.display()
        );
        // A drop must outrank a clean module exit, but must never mask a real error.
        if module_exit_code == 0 {
            return SPEC_EXAMPLE_DROPPED_EXIT;
        }
    }

    module_exit_code
}

/// Parse `path` and return its unconditional example floor, or `None` if the
/// file cannot be read or parsed.
///
/// Gated on a cheap substring probe so that ordinary (non-spec) programs are not
/// re-parsed: a file containing none of the group/example keywords has a floor
/// of zero by construction.
fn declared_example_floor(path: &Path) -> Option<usize> {
    let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    if !matches!(extension, "spl" | "simple" | "sscript" | "") {
        return None;
    }
    let source = std::fs::read_to_string(path).ok()?;
    if !source.contains("describe")
        && !source.contains("context")
        && !source.contains("feature")
        && !source.contains("scenario")
        && !source.contains("it ")
        && !source.contains("it(")
    {
        return Some(0);
    }
    let mut parser = simple_parser::Parser::new(&source);
    let ast = parser.parse().ok()?;
    Some(simple_parser::test_analyzer::unconditional_example_floor(&ast.items))
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
    // Publish argv into the runtime CLI-args storage backing rt_cli_get_args()
    // / rt_cli_arg_count(). Delegated subcommand routes (e.g. `spipe-docgen`)
    // reach this entry without any other publisher, so without this the
    // interpreted app observed argc=0 while the `run` route saw full argv.
    // See doc/08_tracking/bug/spipe_docgen_subcommand_argv_drop_2026-08-16.md.
    if !args.is_empty() {
        simple_runtime::value::rt_set_args_vec(&args);
    }

    if let Some(code) = run_isolated_example_file(path, gc_log, gc_off, &args) {
        return code;
    }

    let path = path.to_path_buf();
    // Kept outside the closure so the panic arm can still name the file it was
    // running when it crashed.
    let path_for_panic = path.clone();
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
            Ok(code) => {
                let results = simple_compiler::interpreter::get_test_results();
                // Order matters: the drop check runs LAST so its `SPEC FILE
                // VERDICT` line is the final stdout line of the run, which is
                // what makes `tail -1` on a spec log authoritative for the FILE
                // instead of for its last `describe`.
                let code = bdd_failure_exit_code(code, &results);
                report_spec_file_verdict(&path, SpecOutcome::Ok, code, &results)
            }
            Err(e) => {
                // The verdict line must exist on EVERY terminal path, and must
                // classify the run. A timeout is UNVERIFIED and gets its own
                // status; an ordinary error keeps the failure status 1.
                let outcome = if watchdog.is_active() && is_timeout_error(&e) {
                    eprintln!("error: {}", timeout_error_message(&path, watchdog.timeout_secs()));
                    SpecOutcome::Timeout
                } else {
                    print_cli_error(&e);
                    SpecOutcome::Error
                };
                let results = simple_compiler::interpreter::get_test_results();
                report_spec_file_verdict(&path, outcome, outcome.exit_code(1), &results)
            }
        }
    }));
    // Engine receipt, emitted on EVERY terminal path of `run` including the
    // crash path -- a run that died is exactly the run whose engine you most
    // want named. Off by default (`SIMPLE_ENGINE_RECEIPT=1`), and costs one
    // environment lookup when off. The engine field it prints was stamped from
    // inside the engine that actually executed; see
    // `simple_common::engine_receipt`.
    simple_common::engine_receipt::emit(&path_for_panic.display().to_string());
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
            // A crashed spec must never be silently omitted from the accounting:
            // emit the same authoritative line, classified CRASHED. Guarded by its
            // own `catch_unwind` because we are already unwinding from one panic
            // and a second one here would abort the process; if the verdict cannot
            // be taken we still exit 101 rather than lose the crash.
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let results = simple_compiler::interpreter::get_test_results();
                report_spec_file_verdict(&path_for_panic, SpecOutcome::Crashed, 101, &results)
            }))
            .unwrap_or(101)
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

    /// Write `source` to a uniquely-named temp `.spl` file and return its path.
    fn spec_fixture(tag: &str, source: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!("simple_dropcheck_{}_{}.spl", tag, std::process::id()));
        std::fs::write(&path, source).expect("write fixture");
        path
    }

    /// The measured drop shape: a bare `return` in the second `describe` body
    /// truncates that group and erases every later group. Five examples are
    /// unconditionally declared, three execute, and before the fix the run was
    /// all-green with exit 0.
    const DROPPING_SPEC: &str = "describe \"alpha\":\n    it \"a1\":\n        expect(1).to_equal(1)\n    it \"a2\":\n        expect(2).to_equal(2)\n\ndescribe \"beta\":\n    return\n    it \"b1\":\n        expect(3).to_equal(3)\n    it \"b2\":\n        expect(4).to_equal(4)\n\ndescribe \"gamma\":\n    it \"g1\":\n        expect(5).to_equal(5)\n";

    #[test]
    fn declared_floor_counts_every_unconditional_example_in_the_dropping_spec() {
        let path = spec_fixture("floor", DROPPING_SPEC);
        let floor = declared_example_floor(&path);
        let _ = std::fs::remove_file(&path);

        assert_eq!(floor, Some(5));
    }

    /// A dropped example must flip a clean exit to a failure. This is the case
    /// that previously exited 0 with an all-green report.
    #[test]
    fn dropped_examples_turn_a_clean_run_into_a_failure() {
        let path = spec_fixture("dropped", DROPPING_SPEC);
        let executed = [
            ex("alpha", "a1", true, false),
            ex("alpha", "a2", true, false),
            ex("gamma", "g1", true, false),
        ];

        let code = report_spec_file_verdict(&path, SpecOutcome::Ok, 0, &executed);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, SPEC_EXAMPLE_DROPPED_EXIT);
        assert_ne!(code, 0);
    }

    /// The inverse, and the cry-wolf guard: a spec that runs everything it
    /// declares must stay green.
    #[test]
    fn a_complete_run_of_the_same_spec_stays_green() {
        let path = spec_fixture("complete", DROPPING_SPEC);
        let executed = [
            ex("alpha", "a1", true, false),
            ex("alpha", "a2", true, false),
            ex("beta", "b1", true, false),
            ex("beta", "b2", true, false),
            ex("gamma", "g1", true, false),
        ];

        let code = report_spec_file_verdict(&path, SpecOutcome::Ok, 0, &executed);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, 0);
    }

    /// Skipped examples are recorded as results, so they are executed, not
    /// dropped. A file whose examples are all skipped must not fail.
    #[test]
    fn skipped_examples_are_not_reported_as_dropped() {
        let path = spec_fixture("skipped", DROPPING_SPEC);
        let executed = [
            ex("alpha", "a1", true, true),
            ex("alpha", "a2", true, true),
            ex("beta", "b1", true, true),
            ex("beta", "b2", true, true),
            ex("gamma", "g1", true, true),
        ];

        let code = report_spec_file_verdict(&path, SpecOutcome::Ok, 0, &executed);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, 0);
    }

    /// Runtime-expanded examples (`it_behaves_like`, loop-generated) mean
    /// executed can legitimately EXCEED the floor. That is never a failure.
    #[test]
    fn executing_more_than_the_floor_is_not_a_failure() {
        let path = spec_fixture("expanded", DROPPING_SPEC);
        let mut executed = vec![
            ex("alpha", "a1", true, false),
            ex("alpha", "a2", true, false),
            ex("beta", "b1", true, false),
            ex("beta", "b2", true, false),
            ex("gamma", "g1", true, false),
        ];
        for i in 0..7 {
            executed.push(ex("gamma", &format!("shared {}", i), true, false));
        }

        let code = report_spec_file_verdict(&path, SpecOutcome::Ok, 0, &executed);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, 0);
    }

    /// An ordinary program is not a spec: no floor, no results, no verdict line,
    /// and its own exit status is preserved untouched.
    #[test]
    fn a_non_spec_program_keeps_its_own_exit_status() {
        let path = spec_fixture("plain", "fn main() -> i64:\n    return 3\n");

        let zero = report_spec_file_verdict(&path, SpecOutcome::Ok, 0, &[]);
        let seven = report_spec_file_verdict(&path, SpecOutcome::Ok, 7, &[]);
        let _ = std::fs::remove_file(&path);

        assert_eq!(zero, 0);
        assert_eq!(seven, 7);
    }

    /// A real error must never be masked by, or downgraded to, a drop status.
    #[test]
    fn a_real_error_outranks_a_drop() {
        let path = spec_fixture("errmask", DROPPING_SPEC);
        let executed = [ex("alpha", "a1", true, false)];

        let code = report_spec_file_verdict(&path, SpecOutcome::Ok, 101, &executed);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, 101);
    }

    /// An unreadable path yields no measurement, and a measurement we could not
    /// take must never be turned into a drop report.
    #[test]
    fn an_unmeasurable_file_never_invents_a_drop() {
        let missing = std::env::temp_dir().join("simple_dropcheck_definitely_absent.spl");
        let _ = std::fs::remove_file(&missing);

        assert_eq!(declared_example_floor(&missing), None);
        assert_eq!(report_spec_file_verdict(&missing, SpecOutcome::Ok, 0, &[]), 0);
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

    // ---- the two-accounting-paths contradiction (2026-08-18) ----

    /// A timeout is UNVERIFIED. It must not land on the spec-example-failure
    /// status, because a consumer classifying by exit status would then book it
    /// as a failure — the exact contradiction with the `Results:` contract.
    #[test]
    fn a_timeout_never_uses_the_spec_failure_status() {
        assert_eq!(SpecOutcome::Timeout.exit_code(1), SPEC_TIMEOUT_EXIT);
        assert_ne!(SPEC_TIMEOUT_EXIT, SPEC_EXAMPLE_FAILURE_EXIT);
        assert_ne!(SPEC_TIMEOUT_EXIT, SPEC_EXAMPLE_DROPPED_EXIT);
        assert_ne!(SPEC_TIMEOUT_EXIT, 0);
    }

    /// The UNVERIFIED classes are exactly TIMEOUT / TERMINATED / NOT_RUN, and the
    /// verified ones exactly OK / ERROR / CRASHED. A SIGKILL is CRASHED, not
    /// TERMINATED, so the two must never share a token.
    #[test]
    fn the_outcome_classes_do_not_collapse_into_each_other() {
        for (outcome, token, verified) in [
            (SpecOutcome::Ok, "OK", true),
            (SpecOutcome::Error, "ERROR", true),
            (SpecOutcome::Crashed, "CRASHED", true),
            (SpecOutcome::Terminated, "TERMINATED", false),
            (SpecOutcome::Timeout, "TIMEOUT", false),
            (SpecOutcome::NotRun, "NOT_RUN", false),
        ] {
            assert_eq!(outcome.as_str(), token);
            assert_eq!(outcome.is_verified(), verified, "{token}");
        }
        assert_ne!(SpecOutcome::Crashed, SpecOutcome::Terminated);
        // Only a normally-completed run can be measured for silent drops.
        assert!(SpecOutcome::Ok.drop_check_applies());
        for outcome in [
            SpecOutcome::Error,
            SpecOutcome::Crashed,
            SpecOutcome::Terminated,
            SpecOutcome::Timeout,
            SpecOutcome::NotRun,
        ] {
            assert!(!outcome.drop_check_applies(), "{}", outcome.as_str());
        }
    }

    /// A spec killed by the watchdog after three of its five examples must NOT be
    /// reported as having dropped two, and must not exit on the drop status.
    #[test]
    fn a_timed_out_spec_is_not_reported_as_dropping_examples() {
        let path = spec_fixture("timeout", DROPPING_SPEC);
        let partial = [
            ex("alpha", "a1", true, false),
            ex("alpha", "a2", true, false),
            ex("beta", "b1", false, false),
        ];

        let code = report_spec_file_verdict(&path, SpecOutcome::Timeout, 1, &partial);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, SPEC_TIMEOUT_EXIT);
        assert_ne!(code, SPEC_EXAMPLE_DROPPED_EXIT);
    }

    /// A crashed spec keeps its crash status and is never downgraded to a drop
    /// report, but is also never silently omitted — it still gets a verdict line.
    #[test]
    fn a_crashed_spec_keeps_its_crash_status() {
        let path = spec_fixture("crashed", DROPPING_SPEC);
        let partial = [ex("alpha", "a1", true, false)];

        let code = report_spec_file_verdict(&path, SpecOutcome::Crashed, 101, &partial);
        let _ = std::fs::remove_file(&path);

        assert_eq!(code, 101);
        assert_ne!(code, 0);
    }

    /// `passed + failed + skipped == executed` must hold, or a reader reconciling
    /// the line against the summary sees a phantom drop. This is what the missing
    /// `skipped=` field cost.
    #[test]
    fn the_verdict_fields_reconcile_with_executed() {
        let results = [
            ex("alpha", "a1", true, false),
            ex("alpha", "a2", false, false),
            ex("beta", "b1", false, true),
        ];
        let executed = bdd_executed_count(&results);
        let (counted, failed) = bdd_example_counts(&results);
        let passed = counted - failed;
        let skipped = executed - counted;

        assert_eq!(passed + failed + skipped, executed);
        assert_eq!((passed, failed, skipped, executed), (1, 1, 1, 3));
    }

    /// The line must stay outside the shape `test_runner_single.spl` sums, or
    /// every count in the repo doubles.
    #[test]
    fn the_verdict_line_shape_cannot_be_summed_as_a_describe_line() {
        let line = format!(
            "SPEC FILE VERDICT: {} outcome={} declared>={} executed={} passed={} failed={} skipped={} dropped={}",
            "x.spl",
            SpecOutcome::Timeout.as_str(),
            5,
            3,
            2,
            0,
            0,
            0
        );
        assert!(!line.contains("examples, "));
        assert!(!line.contains("failures"));
        assert!(line.contains("outcome=TIMEOUT"));
    }
}
