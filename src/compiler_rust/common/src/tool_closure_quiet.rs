//! Quiet switch for load-time diagnostics about a TOOL's own import closure.
//!
//! `simple lint|fix|fmt <file>` runs the pure-Simple linter
//! (`src/app/cli/lint_entry.spl`) on the seed interpreter. The seed loads the
//! linter's whole import closure (compiler + std) before `main` runs, and the
//! loader's advisory diagnostics about THAT closure (`[visibility-warning]`,
//! co-compiled-definition warnings, `warning[enum-bare-name-ambiguous]`,
//! `[gc-warning]`, parser hints) were printed on every lint run: ~400 stderr
//! lines that say nothing about the linted file and bury its findings.
//!
//! The driver sets [`TOOL_CLOSURE_QUIET_ENV`] (and the older
//! `SIMPLE_NO_DEPRECATED_WARNINGS`, which already gates the parser hints and
//! `[gc-warning]`) before it loads the lint entry. The loader's remaining
//! advisory emitters consult [`tool_closure_quiet`]. Errors are never gated,
//! and `run`/`test`/`compile` of user code never set the switch.
//! `SIMPLE_LINT_CLOSURE_DIAGNOSTICS=1` keeps everything on.

/// Set to `1` by the driver while a quiet tool entry is loaded and run.
pub const TOOL_CLOSURE_QUIET_ENV: &str = "SIMPLE_TOOL_CLOSURE_QUIET";
/// User opt-out: `1` restores the tool-closure diagnostics for `lint|fix|fmt`.
pub const LINT_CLOSURE_DIAGNOSTICS_ENV: &str = "SIMPLE_LINT_CLOSURE_DIAGNOSTICS";

/// App entries whose own closure diagnostics are noise for their user.
pub fn app_is_quiet_tool_entry(app_relative_path: &str) -> bool {
    app_relative_path == "src/app/cli/lint_entry.spl"
}

/// Pure decision: should the driver quiet closure diagnostics for this app?
pub fn should_quiet_tool_closure(app_relative_path: &str, closure_diagnostics: Option<&str>) -> bool {
    app_is_quiet_tool_entry(app_relative_path) && closure_diagnostics != Some("1")
}

/// Apply the switch to this process (inherited by lint worker children).
/// Returns whether the switch was applied.
pub fn quiet_tool_closure_for_app(app_relative_path: &str) -> bool {
    let requested = std::env::var(LINT_CLOSURE_DIAGNOSTICS_ENV).ok();
    if !should_quiet_tool_closure(app_relative_path, requested.as_deref()) {
        return false;
    }
    std::env::set_var(TOOL_CLOSURE_QUIET_ENV, "1");
    if std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_none() {
        std::env::set_var("SIMPLE_NO_DEPRECATED_WARNINGS", "1");
    }
    true
}

/// True while advisory diagnostics about a tool's own closure must not print.
pub fn tool_closure_quiet() -> bool {
    std::env::var_os(TOOL_CLOSURE_QUIET_ENV).is_some_and(|v| v == "1")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_lint_entry_is_quieted() {
        assert!(should_quiet_tool_closure("src/app/cli/lint_entry.spl", None));
        assert!(should_quiet_tool_closure("src/app/cli/lint_entry.spl", Some("0")));
        assert!(!should_quiet_tool_closure("src/app/cli/lint_entry.spl", Some("1")));
        assert!(!should_quiet_tool_closure("src/app/test_runner_new/main.spl", None));
        assert!(!should_quiet_tool_closure("src/app/cli/main.spl", None));
    }
}
