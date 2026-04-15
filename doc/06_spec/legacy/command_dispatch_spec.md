# Command Dispatch Specification

*Source: `test/unit/app/tooling/command_dispatch_spec.spl`*
*Last Updated: 2026-03-29*

---

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

### Artifacts

- target/test-artifacts/unit/app/tooling/command_dispatch/summary.txt

### Logs

- target/test-artifacts/unit/app/tooling/command_dispatch/output.log

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 105 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- formatter app path
- lint app path
- sspec_docgen app path
- context app path
- mcp app path
- verify app path
- dashboard app path
- coverage app path
- depgraph app path
- lsp app path
- dap app path
- test_runner_new app path
- all guards follow SIMPLE_<CMD>_RUST pattern
- guard names are uppercase
- guard count matches migrated command count
- no duplicate guard names
- detects --json as Rust-only
- normal args do not need Rust
- EDGE: --json-output is NOT --json (exact match)
- EDGE: --JSON uppercase is NOT --json (case sensitive)
- detects --json as Rust-only
- detects --fix as Rust-only
- both --json and --fix triggers Rust
- normal args do not need Rust
- EDGE: --fixed is NOT --fix (exact match)
- detects --watch as Rust-only
- detects --parallel as Rust-only
- detects -p as Rust-only
- detects --json as Rust-only
- detects --rust-tests as Rust-only
- detects --list-runs as Rust-only
- detects --full-parallel as Rust-only
- detects --rust-ignored as Rust-only
- normal test args do not need Rust
- detects --doctest prefix
- detects --diagram prefix
- detects --seq- prefix
- detects --prune-runs prefix
- EDGE: --watching is NOT --watch (exact match)
- prepends simple_old and app path using slice
- passes all user args preserving order
- handles no extra args (command only)
- EDGE: single arg after command
- EDGE: many args preserved
- EDGE: args with equals signs
- EDGE: args with spaces in values
- EDGE: flag-like filenames
- EDGE: empty string arg
- EDGE: double dash separator
- all migrated apps follow src/app/<name>/main.spl pattern
- test runner uses test_runner_new directory
- EDGE: path does not contain double slashes
- EDGE: path segments are valid identifiers
- EDGE: total migrated app count is 12
- EDGE: each app has unique directory name
- resolve: CWD path is first priority
- resolve: exe-relative goes up two dirs from target/debug
- compile stays in Rust (bootstrapping dependency)
- package management stays in Rust (deep integration)
- EDGE: non-migrated and migrated sets do not overlap
- EDGE: brief uses inline codegen, not dispatch
- coverage has no Rust fallback
- all pure Simple commands listed
- fmt has Rust fallback
- hybrid command count is 8
- hybrid + pure = total migrated
- EDGE: each hybrid command has a matching guard
- EDGE: flag at end of args
- EDGE: flag at beginning (right after command)
- EDGE: flag in middle of args
- EDGE: only flag, no files
- EDGE: multiple non-rust flags
- EDGE: args[1:] skips command name correctly
- EDGE: single letter flag -p matches exactly
- EDGE: -p is not prefix of -pattern
- EDGE: --capture-screenshots exact match
- EDGE: --cleanup-runs exact match
- EDGE: combined rust-only and normal flags
- EDGE: no args at all (just command)
- slice of single-element list is empty
- slice preserves all elements
- slice of two-element list gives one element
- EDGE: nested slicing
- EDGE: slice with negative index
- EDGE: full slice is identity
- EDGE: slice range
- EDGE: step slice
- fmt maps to formatter (not fmt)
- sspec-docgen maps to sspec_docgen (hyphen to underscore)
- test maps to test_runner_new (not test)
- direct name commands: lint, coverage, verify, dashboard, context, mcp, depgraph, lsp, dap
- EDGE: command name is not always the directory name
- EDGE: all app directories are snake_case or single word
- env guard takes highest priority
- rust-only flags take second priority
- simple app used when no env guard and no rust flags
- rust fallback used when app not found
- EDGE: env guard overrides even with no rust flags
- EDGE: app not found with no fallback errors
- simulate fmt dispatch: normal args -> Simple
- simulate fmt dispatch: --json -> Rust
- simulate fmt dispatch: env guard -> Rust
- simulate coverage dispatch: no fallback, app exists -> Simple
- simulate coverage dispatch: no fallback, app missing -> error
- simulate test dispatch: --watch -> Rust, normal -> Simple
