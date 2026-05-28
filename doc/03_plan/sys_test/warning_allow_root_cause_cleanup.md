# System Test Plan: Warning/Allow Root-Cause Cleanup

1. Run `cargo clippy --workspace --all-targets -- -D warnings` from
   `src/compiler_rust/`.
2. Run `bin/simple lint test/system/code_quality/allow_suppressions_spec.spl test/system/code_quality/bare_bool_lint_spec.spl test/system/code_quality/primitive_api_lint_spec.spl test/system/code_quality/warning_allow_root_cause_cleanup_spec.spl --deny-all`.
3. Verify `test/system/code_quality/warning_allow_root_cause_cleanup_spec.spl` stays
   green after workflow changes.
4. Confirm advisory workflows such as `vscode-tests.yml` and
   `electron-tests.yml` remain untouched in this slice.

## Verification Result (2026-05-19)

Status: **PASS** — committed as `461479c0af`.

- All 4 canary specs pass.
- Allow count reduced from 1822 to 1714.
  - `unnamed_duplicate_typed_args`: 1029 → 943
  - `primitive_api`: 222 → 196
  - `bare_bool`: 62 → 52
- 2 known WARNs (not failures):
  - lint wrapper segfault (STATUS=139) — pre-existing, tracked separately
  - `@extern` triggers `unknown_attribute` — root cause deferred per design doc
