# System Test Plan: Warning/Allow Root-Cause Cleanup

1. Run `cargo clippy --workspace --all-targets -- -D warnings` from
   `src/compiler_rust/`.
2. Run `bin/simple lint test/code_quality/allow_suppressions_spec.spl test/code_quality/bare_bool_lint_spec.spl test/code_quality/primitive_api_lint_spec.spl test/code_quality/warning_allow_root_cause_cleanup_spec.spl --deny-all`.
3. Verify `test/code_quality/warning_allow_root_cause_cleanup_spec.spl` stays
   green after workflow changes.
4. Confirm advisory workflows such as `vscode-tests.yml` and
   `electron-tests.yml` remain untouched in this slice.
