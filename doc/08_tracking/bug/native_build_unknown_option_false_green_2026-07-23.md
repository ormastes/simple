# BUG: native-build ignored unknown options

## Verification note 2026-11-25 — fix confirmed present on release/1.0.0

- **inspected**: `cli_native_build_option_error` is defined at
  `src/app/io/_CliCompile/compile_targets.spl:374` and called from the
  native-build path at `:1335`; its closed fallback
  `elif arg.starts_with("-"): return "unknown option: {arg}"` (`:529-530`)
  rejects any unrecognized `-` token — including the `--entry-clousre`
  misspelling from the repro — before compilation. The regression spec
  `test/01_unit/app/compile/cli_native_build_spec.spl` exists.
- **limit**: the regression spec is not runnable on this host — the Rust seed
  (v1.0.0-rc.1) rejects `@representation_boundary` in imported stdlib modules
  (`env_get_nilable`), so the CLOSED status is confirmed by code inspection,
  not re-execution.

## Closed 2026-09-16 — ...ack for a token starting with `-`. ## Fix and regression `cli_native_build_option_error` v

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Reproduction

Append `--entry-clousre` to an otherwise valid pure-Simple `native-build`
command. Before the fix, the parser ignored it and could publish a binary with
exit 0 instead of rejecting the misspelling.

## Root cause

`cli_native_build` decoded known flags but had no closed fallback for a token
starting with `-`.

## Fix and regression

`cli_native_build_option_error` validates supported forms and required values
before compilation. `test/01_unit/app/compile/cli_native_build_spec.spl`
checks unknown, option-looking missing values, and invalid worker counts
without invoking the compiler.

## Policy

A sole help flag exits 0. Any malformed argument list, including one that also
contains help, exits 2 before the worker or output staging is reached.

